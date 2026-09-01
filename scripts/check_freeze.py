#!/usr/bin/env python3
"""Fail closed if the solver, ledgers, provenance, or submission layout drift."""

from __future__ import annotations

import ast
import hashlib
import json
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SUBMISSION = ROOT / "submission"
SOLVER = SUBMISSION / "solver.py"
PROVENANCE = ROOT / "PROVENANCE.json"
MAX_SOLVER_BYTES = 500_000
REQUIRED_PROMPT_FIELDS = {
    "{problem.equation1}",
    "{problem.equation2}",
    "{history.attempts}",
    "{solver.hint}",
}


class FreezeError(ValueError):
    pass


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_json(path: Path):
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise FreezeError(f"invalid JSON artifact: {path.relative_to(ROOT)}") from error


def check_submission(provenance: dict) -> None:
    entries = sorted(path.name for path in SUBMISSION.iterdir())
    if entries != ["solver.py"]:
        raise FreezeError(f"submission directory differs: {entries}")
    source = SOLVER.read_text(encoding="utf-8")
    payload = source.encode("utf-8")
    if len(payload) > MAX_SOLVER_BYTES:
        raise FreezeError("solver exceeds the official 500000-byte limit")
    if len(payload) != provenance["solver_py_bytes"]:
        raise FreezeError("solver byte count differs from provenance")
    if sha256(SOLVER) != provenance["solver_py_sha256"]:
        raise FreezeError("solver SHA-256 differs from provenance")
    tree = ast.parse(source, filename=str(SOLVER))
    prompt = None
    for node in tree.body:
        if isinstance(node, (ast.Assign, ast.AnnAssign)):
            targets = node.targets if isinstance(node, ast.Assign) else [node.target]
            if any(isinstance(target, ast.Name) and target.id == "PROMPT" for target in targets):
                value = node.value
                if isinstance(value, ast.Constant) and isinstance(value.value, str):
                    prompt = value.value
                    break
    if prompt is None:
        raise FreezeError("top-level string PROMPT is missing")
    missing = sorted(REQUIRED_PROMPT_FIELDS - {field for field in REQUIRED_PROMPT_FIELDS if field in prompt})
    if missing:
        raise FreezeError(f"PROMPT placeholders missing: {missing}")


def ledger_stats(path: Path) -> dict:
    rows = load_json(path)
    if not isinstance(rows, list) or not rows:
        raise FreezeError(f"ledger is not a nonempty array: {path.relative_to(ROOT)}")
    solved = [row for row in rows if row.get("solved") is True]
    for row in solved:
        if row.get("llm_calls", 0) != 0:
            raise FreezeError(f"accepted row attributes an LLM call: {row.get('id')}")
        if not isinstance(row.get("code"), str) or not row["code"].strip():
            raise FreezeError(f"accepted row has no certificate code: {row.get('id')}")
    return {
        "accepted": len(solved),
        "total": len(rows),
        "llm_calls": sum(int(row.get("llm_calls", 0)) for row in rows),
        "judge_calls": sum(int(row.get("judge_calls", 0)) for row in rows),
        "failed_ids": [row.get("id") for row in rows if row.get("solved") is not True],
    }


def check_ledgers(provenance: dict) -> None:
    records = provenance["archived_deterministic_regression"]
    for label, record in records.items():
        path = ROOT / record["ledger"]
        if sha256(path) != record["ledger_sha256"]:
            raise FreezeError(f"{label} ledger SHA-256 differs")
        stats = ledger_stats(path)
        for field in ("accepted", "total", "llm_calls", "judge_calls"):
            if stats[field] != record[field]:
                raise FreezeError(f"{label} {field} differs: {stats[field]} != {record[field]}")
    report = (ROOT / "results" / "FINAL_DETERMINISTIC_REGRESSION.md").read_text(encoding="utf-8")
    if provenance["solver_py_sha256"] not in report:
        raise FreezeError("final regression report does not bind the current solver")
    # The displayed regression table must match the committed ledgers: every
    # bound ledger's 16-hex prefix and wall-clock sum must appear verbatim.
    for label, record in provenance["archived_deterministic_regression"].items():
        prefix = record["ledger_sha256"][:16]
        if prefix not in report:
            raise FreezeError(
                f"regression report is missing the {label} ledger prefix {prefix}"
            )
        wall = str(record["wall_clock_sum_s"])
        if wall not in report:
            raise FreezeError(
                f"regression report wall-clock for {label} ({wall}) not found"
            )

    latest_records = provenance["latest_upstream_validation"][
        "deterministic_regression"
    ]
    for label, record in latest_records.items():
        path = ROOT / record["ledger"]
        if sha256(path) != record["ledger_sha256"]:
            raise FreezeError(f"latest-upstream {label} ledger SHA-256 differs")
        stats = ledger_stats(path)
        for field in ("accepted", "total", "llm_calls", "judge_calls"):
            if stats[field] != record[field]:
                raise FreezeError(
                    f"latest-upstream {label} {field} differs: "
                    f"{stats[field]} != {record[field]}"
                )


def main() -> int:
    try:
        provenance = load_json(PROVENANCE)
        if provenance.get("official_repo") != (
            "https://github.com/SAIRcompetition/equational-theories-lean-stage2"
        ):
            raise FreezeError("official repository differs")
        check_submission(provenance)
        check_ledgers(provenance)
    except (FreezeError, OSError, KeyError, TypeError, ValueError) as error:
        print(f"FAIL: {error}")
        return 1
    print(
        "PASS: submission layout, solver hash, prompt, provenance, and final ledgers are bound"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
