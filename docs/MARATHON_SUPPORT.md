# Marathon-track support

`submission/solver.py` remains one dual-mode, standard-library-only file.
With no Marathon environment variable it enters the original Solo `main()` and
uses the unchanged stdin/stdout JSON protocol. When
`JUDGE_MARATHON_MANIFEST` is present, the final `__main__` dispatch instead
calls `run_marathon()`.

## Official trigger and output contract

The Marathon path reads the runner-owned JSONL manifest named by
`JUDGE_MARATHON_MANIFEST` and appends answer rows to the path named by
`JUDGE_MARATHON_OUTPUT`. Each row has the official shape:

```json
{"id":"normal_0042","verdict":"true","code":"<full Lean source>"}
```

Every answer is written as one JSON line, flushed, and `fsync`ed before the
next problem starts. A runner SIGTERM therefore leaves all complete earlier
rows available to the post-run scorer.

Marathon has no interactive judge-call channel. As specified by the official
runner and demonstrated by all three reference solvers, the runner scores the
last complete row for each ID with `verify_answer` after the solver exits. The
batch driver emits the same first deterministic certificates used by the Solo
path; the frozen public regression evidence records one judge call and an
accepted result for every one of the 1,889 public rows.

## Scheduling and budget management

Problems are stably sorted by a cheap structural cost (operation and variable
counts, then equation length). A single monotonic global deadline is derived
from `JUDGE_MARATHON_BUDGET_SECONDS`, with a small tail reserved for the last
durable output write.

Before each problem, its fair cap is recomputed from remaining wall time divided
by remaining problems, clamped to 30--300 seconds. The work deadline is also
clamped to the global deadline, which matters for deliberately compressed local
budgets where even the 30-second floor cannot fit every problem. A Marathon-only
`setitimer` alarm enforces the entire slice, including legacy searches whose
inner loops predate the batch driver.

Scheduling has two passes:

1. Every problem receives the original cheap deterministic stages 1--3:
   structured countermodels, direct/singleton/quick-superposition proofs, and
   the bounded irregular finite-model search. This pass makes no LLM calls and
   appends each certificate immediately.
2. Only residual problems receive stages 4--5: deeper structured/model search,
   then the anytime proof-producing superposition pass. The false side receives
   at most 55% of the dynamically computed slice, preserving time for the true
   side and for later residuals.

The public deterministic floor is already complete, so Marathon deliberately
does not spend LLM tokens on speculative residual answers.

## Validation

Validation targets the official checkout at revision
`2848228ff490422442878fd6f5abaf4cfa95257d` and does not modify that checkout.
The exact commands are:

```bash
cd /Users/lexa/Desktop/lexa/omega/eqt2-stage2
source .env.judge
export JUDGE_ARTIFACT_DIR=/tmp/sair-v2-marathon-judge-artifacts
PYTHONDONTWRITEBYTECODE=1 .venv/bin/python3 scripts/run_marathon.py \
  --solver /Users/lexa/Desktop/lexa/omega/sair-v2-marathon/submission \
  --manifest tests/marathon_fixtures/manifests/normal_5.jsonl \
  --output-dir /tmp/sair-v2-marathon-normal-5

PYTHONDONTWRITEBYTECODE=1 .venv/bin/python3 scripts/run_marathon.py \
  --solver /Users/lexa/Desktop/lexa/omega/sair-v2-marathon/submission \
  --manifest examples/problems/marathon/normal_100.jsonl \
  --budget-seconds 600 --budget-tokens 0 \
  --output-dir /tmp/sair-v2-marathon-normal-100

PYTHONDONTWRITEBYTECODE=1 .venv/bin/python3 -m pipeline.runner \
  --submission /Users/lexa/Desktop/lexa/omega/sair-v2-marathon/submission \
  --problems examples/problems/sample_20.json \
  --output /tmp/sair-v2-marathon-solo-sample-20.json
```

### Measured results (2026-08-20)

- `normal_5.jsonl`: 5/5 accepted, 5 attempted, 0 not attempted; solver wall
  11.6 seconds, zero LLM tokens, clean exit with no SIGTERM/SIGKILL.
- External-solver Marathon harness manifest: `marathon_llm.imports` and
  `external_solver_normal_5` both passed (2 passed, 0 failed, Lean on). The
  stock harness has no `--solver` option; this used its supported `--manifest`
  option with an absolute `submission_path` in a temporary one-case manifest.
- `normal_100.jsonl`, reduced 600-second wall budget and zero-token budget:
  100/100 accepted, 100 attempted, 0 not attempted; solver wall 161.7 seconds,
  clean exit with no SIGTERM/SIGKILL.
- Solo `sample_20.json`: 20/20 solved, 0 failed in 68.0 seconds. Every problem
  used one judge call and zero LLM calls.

The first fixture attempt reached scoring but the managed workspace denied a
write to the official checkout's default `.artifacts` directory. Redirecting
only `JUDGE_ARTIFACT_DIR` to `/tmp` resolved that sandbox restriction; the
official checkout and its judge sources remained unchanged.
