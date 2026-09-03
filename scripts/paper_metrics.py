#!/usr/bin/env python3
"""Recompute the certificate-size and judge-time table from bound ledgers."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
PUBLIC = [
    "results/v2_sample_20_official_2848228.json",
    "results/v2_sample_200_official_2848228.json",
    "results/v2_hard1_official_2848228.json",
    "results/v2_hard2_official_2848228.json",
    "results/v2_hard3_official_2848228.json",
    "results/v2_normal_official_2848228.json",
]
HOLDOUT = ["results/stage2_stress_test_results.json"]
OUTPUT = ROOT / "results" / "paper_certificate_metrics.json"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def percentile(values: list[float | int], fraction: float) -> float | int:
    ordered = sorted(values)
    return ordered[min(len(ordered) - 1, int(len(ordered) * fraction))]


def accepted_check_time(row: dict) -> float:
    events = [
        event["elapsed"]
        for event in row.get("log", [])
        if event.get("type") == "judge"
        and event.get("response", {}).get("status") == "accepted"
    ]
    if not events:
        raise ValueError(f"accepted judge event missing for {row.get('id')}")
    return events[-1]


def summarize(paths: list[str]) -> dict:
    rows = []
    for relative in paths:
        rows.extend(json.loads((ROOT / relative).read_text(encoding="utf-8")))
    result = {}
    for verdict in ("false", "true"):
        selected = [row for row in rows if row.get("verdict") == verdict]
        cert_bytes = [len(row["code"].encode("utf-8")) for row in selected]
        check_seconds = [accepted_check_time(row) for row in selected]
        wall_seconds = [row["elapsed_seconds"] for row in selected]
        result[verdict] = {
            "n": len(selected),
            "certificate_bytes": {
                "median": percentile(cert_bytes, 0.5),
                "p95": percentile(cert_bytes, 0.95),
                "max": max(cert_bytes),
            },
            "accepted_judge_event_seconds": {
                "median": percentile(check_seconds, 0.5),
                "p95": percentile(check_seconds, 0.95),
                "max": max(check_seconds),
            },
            "end_to_end_wall_seconds": {
                "median": percentile(wall_seconds, 0.5),
                "p95": percentile(wall_seconds, 0.95),
                "max": max(wall_seconds),
            },
        }
    return result


def main() -> None:
    sources = PUBLIC + HOLDOUT
    payload = {
        "method": "UTF-8 certificate bytes; upper median; index floor(0.95*n) for p95; final accepted judge event",
        "source_ledgers": {relative: sha256(ROOT / relative) for relative in sources},
        "public_six_sets": summarize(PUBLIC),
        "temporal_holdout": summarize(HOLDOUT),
    }
    OUTPUT.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
