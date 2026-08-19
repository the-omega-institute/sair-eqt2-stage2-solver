#!/usr/bin/env python3
"""Benchmark the solver's TRUE-side prover (general_true_cert / g3_prove)
on the TRUE problems of a public set, optionally judging every certificate.

usage:
  python3 scripts/bench_true_prover.py --judge-repo /path/to/eqt2-stage2 \
      --set hard3 [--budget 30] [--judge] [--fn g3_prove] [--workers 10]

--set accepts hard1|hard2|hard3|normal (jsonl under <judge-repo>/examples/problems)
or a path to a JSON list / JSONL file of problems.  Run with the judge repo's
venv python and `source .env.judge` when --judge is given.
"""
import argparse
import importlib.util
import json
import os
import sys
import time
from concurrent.futures import ProcessPoolExecutor, as_completed

HERE = os.path.dirname(os.path.abspath(__file__))
SOLVER = os.path.join(HERE, "..", "submission", "solver.py")


def load_problems(judge_repo, name):
    path = name
    if not os.path.exists(path):
        path = os.path.join(judge_repo, "examples", "problems", name + ".jsonl")
    text = open(path).read()
    if text.lstrip().startswith("["):
        probs = json.loads(text)
    else:
        probs = [json.loads(l) for l in text.splitlines() if l.strip()]
    return [p for p in probs if p.get("answer") is True]


def work(args):
    problem, fn, budget, judge_repo, do_judge = args
    spec = importlib.util.spec_from_file_location("solver", SOLVER)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    started = time.monotonic()
    cert = getattr(mod, fn)(problem["equation1"], problem["equation2"], time_budget_s=budget)
    out = {"id": problem["id"], "t": round(time.monotonic() - started, 2),
           "found": cert is not None, "bytes": len(cert) if cert else 0}
    if cert and do_judge:
        sys.path.insert(0, judge_repo)
        sys.path.insert(0, os.path.join(judge_repo, "pipeline"))
        from judge.verify import verify_answer, JudgeConfig  # noqa
        from proxy import DEFAULT_PROOF_POLICY  # noqa
        import pathlib
        config = JudgeConfig(lake_bin=pathlib.Path(os.environ.get("LAKE_BIN", "lake")),
                             lean_bin=pathlib.Path(os.environ.get("LEAN_BIN", "lean")),
                             lean_timeout_seconds=300)
        p = dict(problem)
        p["proof_policy"] = DEFAULT_PROOF_POLICY
        t2 = time.monotonic()
        res = verify_answer(p, json.dumps({"verdict": "true", "code": cert}), config=config)
        out["status"] = res.get("status")
        out["judge_s"] = round(time.monotonic() - t2, 1)
        if out["status"] != "accepted":
            out["detail"] = (res.get("detail") or res.get("message") or "")[:300]
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--judge-repo", required=True)
    ap.add_argument("--set", required=True)
    ap.add_argument("--budget", type=float, default=30.0)
    ap.add_argument("--fn", default="general_true_cert")
    ap.add_argument("--judge", action="store_true")
    ap.add_argument("--workers", type=int, default=10)
    a = ap.parse_args()
    probs = load_problems(a.judge_repo, a.set)
    results = []
    t0 = time.monotonic()
    with ProcessPoolExecutor(max_workers=a.workers) as ex:
        futs = [ex.submit(work, (p, a.fn, a.budget, a.judge_repo, a.judge)) for p in probs]
        for f in as_completed(futs):
            r = f.result()
            results.append(r)
            print(json.dumps(r), flush=True)
    found = sum(1 for r in results if r["found"])
    acc = sum(1 for r in results if r.get("status") == "accepted")
    print(f"SUMMARY set={a.set} n={len(results)} found={found} accepted={acc} "
          f"wall={time.monotonic() - t0:.0f}s sum_t={sum(r['t'] for r in results):.0f}s")
    print("UNSOLVED", [r["id"] for r in results if not r["found"]])
    print("REJECTED", [(r["id"], r.get("detail")) for r in results
                       if r["found"] and r.get("status") not in (None, "accepted")])


if __name__ == "__main__":
    main()
