#!/usr/bin/env python3
"""Prover-only benchmark of the G3 superposition prover (g3_prove) on a
problem file (JSON list or JSONL); only TRUE problems are run.

usage:
  python3 scripts/bench_g3_sets.py --problems scripts/data/etp_vampire_hard.json \
      [--budget 30] [--workers 8] [--solver submission/solver.py] [--out results.json]

Data sets shipped with the repo:
  scripts/data/v2_true_residuals.json   11 TRUE residuals of the frozen solver
                                        (incl. hard3_0314 = 2923 -> 1623)
  scripts/data/etp_vampire_hard.json    254 implications whose Equational
                                        Theories Project Vampire proof has
                                        >= 12 derivation steps
The public sets live in <judge-repo>/examples/problems/*.jsonl.
"""
import argparse
import importlib.util
import json
import os
import sys
import time
from concurrent.futures import ProcessPoolExecutor, as_completed

HERE = os.path.dirname(os.path.abspath(__file__))


def load_problems(path):
    text = open(path).read()
    if text.lstrip().startswith("["):
        probs = json.loads(text)
    else:
        probs = [json.loads(l) for l in text.splitlines() if l.strip()]
    return [p for p in probs if p.get("answer") is True]


def work(args):
    solver, problem, budget = args
    spec = importlib.util.spec_from_file_location("solver", solver)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    stats = []
    started = time.monotonic()
    cert = mod.g3_prove(problem["equation1"], problem["equation2"],
                        time_budget_s=budget, stats=stats)
    return {"id": problem["id"], "t": round(time.monotonic() - started, 3),
            "found": cert is not None, "bytes": len(cert) if cert else 0,
            "selected": sum(s["selected"] for s in stats),
            "generated": sum(s["generated"] for s in stats),
            "rounds": [(s["size_cap"], s["selected"], s["secs"]) for s in stats]}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--problems", required=True)
    ap.add_argument("--budget", type=float, default=30.0)
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--solver", default=os.path.join(HERE, "..", "submission", "solver.py"))
    ap.add_argument("--out", default=None)
    a = ap.parse_args()
    probs = load_problems(a.problems)
    results = []
    t0 = time.monotonic()
    with ProcessPoolExecutor(max_workers=a.workers) as ex:
        futs = [ex.submit(work, (a.solver, p, a.budget)) for p in probs]
        for f in as_completed(futs):
            r = f.result()
            results.append(r)
            if not r["found"] or r["t"] > 1.0:
                print(json.dumps(r), flush=True)
    results.sort(key=lambda r: r["id"])
    ts = sorted(r["t"] for r in results)
    found = sum(1 for r in results if r["found"])
    print(f"SUMMARY problems={a.problems} n={len(results)} found={found} "
          f"median={ts[len(ts) // 2]:.3f}s p90={ts[int(len(ts) * 0.9)]:.3f}s "
          f"max={ts[-1]:.2f}s sum={sum(ts):.1f}s wall={time.monotonic() - t0:.0f}s")
    print("UNSOLVED", [r["id"] for r in results if not r["found"]])
    if a.out:
        json.dump(results, open(a.out, "w"), indent=1)


if __name__ == "__main__":
    main()
