#!/usr/bin/env python3
"""Probe the official judge with a (problem, verdict, lean code) triple and time it.

Usage: judge_probe.py <problem.json> <verdict> <cert.lean>
"""
import json, os, subprocess, sys, time, pathlib, tempfile
JUDGE = "/Users/lexa/Desktop/lexa/omega/eqt2-stage2"
prob = json.load(open(sys.argv[1]))
verdict = sys.argv[2]
code = open(sys.argv[3]).read()
tmp = pathlib.Path(tempfile.mkdtemp(prefix="probe_"))
(tmp/"p.json").write_text(json.dumps(prob))
(tmp/"a.json").write_text(json.dumps({"verdict": verdict, "code": code}))
env = dict(os.environ, LEAN_BIN="/Users/lexa/.elan/bin/lean", LAKE_BIN="/Users/lexa/.elan/bin/lake",
           PATH=os.path.expanduser("~/.elan/bin") + ":" + os.environ["PATH"], PYTHONDONTWRITEBYTECODE="1")
t0 = time.time()
r = subprocess.run([f"{JUDGE}/.venv/bin/python3", "verify_one.py", str(tmp/"p.json"), str(tmp/"a.json")],
                   cwd=JUDGE, env=env, capture_output=True, text=True)
dt = time.time() - t0
print(json.dumps({"time_s": round(dt, 2), "stdout": r.stdout.strip()[-2000:], "stderr": r.stderr.strip()[-1500:]}))
