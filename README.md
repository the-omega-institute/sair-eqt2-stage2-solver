# SAIR EQT2 Stage 2 solver

Private collaboration repository for the Omega Institute entry to the SAIR
Mathematics Distillation Challenge, Equational Theories Stage 2.

The only competition-submittable artifact is
[`submission/solver.py`](submission/solver.py). The submission directory is
kept deliberately single-file because the official Solo runner rejects helper
files placed beside `solver.py`.

## Current evidence

All scores below are local official-runner measurements (official revision
`2848228`), not hosted leaderboard scores. Every accepted row contains a Lean
certificate accepted by the official judge and was produced before the LLM
fallback (`llm_calls = 0`).

| Problem set | Accepted (solver v2.2) | Accepted (superseded v1) |
|---|---:|---:|
| `sample_20` | 20/20 | 20/20 |
| `sample_200` | 200/200 | 196/200 |
| `hard1` | 69/69 | 68/69 |
| `hard2` | 200/200 | 197/200 |
| `hard3` | 400/400 | 394/400 |
| `normal` | 1000/1000 | 1000/1000 |
| total | **1889/1889** | 1875/1889 |
| Marathon `normal_100` (canonical manifest) | 100/100, 0 tokens | — |

The full ledgers, exact failed IDs, call counts, hashes, and wall-clock totals
are recorded in
[`results/FINAL_DETERMINISTIC_REGRESSION.md`](results/FINAL_DETERMINISTIC_REGRESSION.md)
and [`PROVENANCE.json`](PROVENANCE.json). A separate fixed-configuration live
measurement of the organizer-pinned `gpt-oss-120b` fallback solved 0/6 original
`sample_20` residuals of v1; see [`docs/LIVE_RUN_NOTES.md`](docs/LIVE_RUN_NOTES.md).

## Solver architecture

The single-file solver orders proof-producing stages from cheapest to most
expensive:

1. explicit finite-magma countermodels over small carriers, linear/affine
   magmas mod n (n ≤ 50), F_p^k vector-linear and polynomial families;
2. singleton, substitution-instance and quick superposition true proofs;
3. finite-model search with Latin-square propagation over carriers 4–10
   (`finOpTable` witnesses for n ≤ 10, `submission.op` arithmetic certificates
   for larger carriers) and canned ℕ-carrier models for known Austin pairs;
4. deep anytime ordered unit-superposition prover for true implications, with
   robust re-emission and a lemma-pool + `grind` fallback;
5. organizer-mediated `gpt-oss-120b` fallback, with every proposal sent to the
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
