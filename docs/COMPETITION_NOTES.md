# Official SAIR EQT2 Stage 2 competition notes

This repository contains the private competition solver and its evidence. The
only uploadable artifact is `submission/solver.py`; no result ledger, paper
file, helper test, or provenance file belongs in the hosted submission.

## Current official contract

- Competition status checked on 2026-08-17: active.
- Deadline: 2026-08-31 23:59 AoE (2026-09-01 11:59:59 UTC).
- Submission: one `solver.py`, at most 500,000 bytes.
- Local runner scores are not hosted leaderboard results.
- The repository remains private before the deadline.
- Uploading to SAIR and making this repository public each require a separate
  explicit human decision.

The latest reviewed official revision is
`2848228ff490422442878fd6f5abaf4cfa95257d`. It clarifies that infinite
carriers are valid for false certificates, aligns Solo token-budget semantics,
and permits non-human-readable datasets when their methodology is disclosed.
The official platform/validator issue remains tracked upstream as issue #3.

## Validated evidence

The complete official harness passed with zero failures under `2848228` on
2026-08-17 and again on the operator host on 2026-08-20. Solver v2
(`29ba1ec8…`) scored 20/20 `sample_20`, 200/200 `sample_200`, 69/69 `hard1`,
200/200 `hard2`, 399/400 `hard3`, 1000/1000 `normal` (1888/1889). All accepted
rows were produced before the LLM fallback and accepted by the Lean judge; the
single failed row (`hard3_0314`) entered a no-key fallback and produced no
model certificate. The superseded v1 solver (`ea2946fe…`) scored 1875/1889.

The same scores were first archived under official revision `6805e232`. The
failed-ID sets match exactly across both revisions. `PROVENANCE.json` binds
both environments to their exact solver, runner configuration, and ledger
hashes; `results/LATEST_UPSTREAM_REGRESSION.md` records the newer replay.

The organizer-pinned live `gpt-oss-120b` experiment is already complete for
the original six `sample_20` residuals: it solved 0/6. See
`docs/LIVE_RUN_NOTES.md`. This is a bounded negative measurement, not a general
claim about LLM theorem proving.

## Reproduce the latest local check

Clone this private repository and an independent official judge checkout:

```bash
git clone https://github.com/the-omega-institute/sair-eqt2-stage2-solver.git
git clone https://github.com/SAIRcompetition/equational-theories-lean-stage2.git
cd equational-theories-lean-stage2
git checkout 2848228ff490422442878fd6f5abaf4cfa95257d
bash scripts/setup.sh
python3 scripts/run_harness.py
```

Then run the frozen solver. `PYTHONDONTWRITEBYTECODE=1` is required so Python
does not create `submission/__pycache__`, which the strict single-file layout
check correctly rejects.

```bash
export SAIR_SOLVER_REPO=/path/to/sair-eqt2-stage2-solver
PYTHONDONTWRITEBYTECODE=1 .venv/bin/python3 -m pipeline.runner \
  --submission "$SAIR_SOLVER_REPO/submission" \
  --problems examples/problems/sample_20.json \
  --output /tmp/sample_20_replay.json
```

No API key is needed for the archived 20/20 path because every problem is
solved before the LLM fallback.

## Remaining gates

- Israel reviews the exact solver hash, latest rules/harness compliance,
  evidence traceability, and competition-paper claim boundary.
- A human confirms the track and uploads the frozen `submission/solver.py`.
- The hosted submission timestamp, solver hash, score, and public result URL
  are recorded only after the platform returns them.
- Paper authorship, order, venue, and release timing remain explicit human
  decisions.
