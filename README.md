# SAIR EQT2 Stage 2 solver

Private collaboration repository for the Omega Institute entry to the SAIR
Mathematics Distillation Challenge, Equational Theories Stage 2.

The only competition-submittable artifact is
[`submission/solver.py`](submission/solver.py). The submission directory is
kept deliberately single-file because the official Solo runner rejects helper
files placed beside `solver.py`.

## Current evidence

All scores below are local official-runner measurements, not hosted leaderboard
scores. Every accepted row contains a Lean certificate accepted by the official
judge.

| Problem set | Accepted | LLM contribution |
|---|---:|---|
| `sample_20` | 20/20 | None; all accepted before fallback |
| `sample_200` | 196/200 | None; all accepted before fallback |
| `hard2` | 197/200 | None; all accepted before fallback |

The full ledgers, exact failed IDs, call counts, hashes, and wall-clock totals
are recorded in
[`results/FINAL_DETERMINISTIC_REGRESSION.md`](results/FINAL_DETERMINISTIC_REGRESSION.md)
and [`PROVENANCE.json`](PROVENANCE.json). A separate fixed-configuration live
measurement of the organizer-pinned `gpt-oss-120b` fallback solved 0/6 original
`sample_20` residuals; see [`docs/LIVE_RUN_NOTES.md`](docs/LIVE_RUN_NOTES.md).

The three full-set measurements were archived under official revision
`6805e232`. On 2026-08-17, the complete official harness and `sample_20` were
rerun against newer official revision `2848228`: the harness was green with
zero failures and the frozen solver remained 20/20 with zero LLM calls. The
`sample_200` and `hard2` scores have not been relabeled as results from the
newer revision.

## Solver architecture

The single-file solver orders proof-producing stages from cheapest to most
expensive:

1. explicit finite-magma countermodels over small carriers;
2. structured polynomial magma countermodels;
3. singleton and substitution-instance true proofs;
4. bounded finite-model search with emitted `finOpTable` witnesses;
5. proof-producing superposition for true implications;
6. organizer-mediated `gpt-oss-120b` fallback, with every proposal sent to the
   Lean judge before acceptance.

The solver never reads an API key, opens repository files, shells out, or calls
the judge outside the official stdin/stdout protocol.

## Validation

Run the repository-local immutable-evidence checks:

```bash
python3 scripts/check_freeze.py
python3 -m unittest discover -s tests -v
```

The official judge and runner are external. Their exact revision and config
hash are recorded in `PROVENANCE.json`; local results must never be relabeled
as hosted competition results.

## Publication boundary

This repository supports a separate SAIR competition solver paper. It is not
the unified FiberRing + SAIR-EQT2 + FATE-X TMLR/JMLR manuscript and not the FKST
systems paper. Authorship, ordering, target venue, and any post-competition
leaderboard claims remain open until explicitly agreed and evidenced.

The repository remains private before the competition deadline. Creating this
repository, running local validation, or reviewing a pull request does not
submit the solver to SAIR.
