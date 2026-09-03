# Anonymous artifact for the CPP 2027 submission

This archive accompanies *A Dual-Polarity Certifying Cascade for Equational
Implication: Lean Proofs and Countermodels under Resource Bounds*.  It contains
the frozen single-file solver, the result ledgers used by the paper, the
temporal-holdout and research-boundary ledgers, and scripts that verify the
artifact identity and recompute the certificate-cost table.

The `official_inputs/` directory contains the `normal_5` and `normal_100`
Marathon manifests and the `sample_20` and `sample_200` Solo inputs copied from
the pinned official checkout.  The remaining official inputs and the judge
implementation stay in that external checkout.

## Frozen identity

- Solver: `submission/solver.py`
- Size: 189,504 UTF-8 bytes
- SHA-256: `f2392533c9f4c03b292be80bc6d12e98e5254cc4861d1cc4b227957ad5ed89b4`
- Freeze commit: `7b636bc3c3e8f4eed80fea1809ba940af3c466f0`
- Freeze time: 2026-08-26 21:31:32 UTC
- Official judge revision: `2848228ff490422442878fd6f5abaf4cfa95257d`
- Local toolchain: Lean 4.30.0-rc2, Mathlib `896cc56a`
- Hosted revalidation: `13648682a5553717ea91b86513ed140b39160cf5`,
  Lean 4.33.1, Mathlib `0df444a3`

The archive's `PROVENANCE.json` preserves the evidence fields from the source
repository but replaces personal team and branch-owner text with anonymous
labels.  Hashes, byte counts, revisions, dates, measurements, and artifact
paths are unchanged.

## Integrity and paper metrics

Run from the archive root:

```sh
python3 scripts/check_freeze.py
python3 scripts/paper_metrics.py
python3 scripts/check_freeze.py
```

The first and third commands must print:

```text
PASS: submission layout, solver hash, prompt, provenance, and final ledgers are bound
```

Recomputing the metrics must produce
`results/paper_certificate_metrics.json` with SHA-256
`56f233426fd6300911b109880915fca5a2c888acf777b3f55224b189003435f9`.
The generator records the SHA-256 of every source ledger in that JSON file.

## Judge replay

The judge is not bundled.  Obtain the official Stage 2 repository, check out
revision `2848228ff490422442878fd6f5abaf4cfa95257d`, and run its documented
setup.  A representative Solo replay from the judge checkout is:

```sh
bash scripts/setup.sh
python3 scripts/run_harness.py
PYTHONDONTWRITEBYTECODE=1 .venv/bin/python3 -m pipeline.runner \
  --submission /absolute/path/to/this/archive/submission \
  --problems examples/problems/sample_20.json \
  --output /tmp/sample_20_replay.json
```

The submission directory must contain only `solver.py`.  No API key is needed
for the archived deterministic results because every accepted row completed
before the language-model fallback.

A representative Marathon replay is:

```sh
source .env.judge
export JUDGE_ARTIFACT_DIR=/tmp/sair-marathon-judge-artifacts
PYTHONDONTWRITEBYTECODE=1 .venv/bin/python3 scripts/run_marathon.py \
  --solver /absolute/path/to/this/archive/submission \
  --manifest examples/problems/marathon/normal_100.jsonl \
  --budget-seconds 600 --budget-tokens 0 \
  --output-dir /tmp/sair-marathon-normal-100
```

## Evidence boundary

The six public ledgers are development-regression evidence.  The solver was
frozen before the official stress set dated 2026-08-28; the byte-identical
artifact then produced 200/200 accepted certificates with zero language-model
calls.  The unscored order-five research set produced 0/100 within budget and
is included as a negative coverage boundary.

The archive does not claim completeness, a hosted leaderboard score,
cross-system superiority, peak-memory measurements, or a controlled component
ablation.  Hosted-playground observations are operator attestations rather
than repository-replayable ledgers.
