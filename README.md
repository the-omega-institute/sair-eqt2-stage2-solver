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

| Problem set | Accepted (solver v2.4) | Accepted (superseded v1) |
|---|---:|---:|
| `sample_20` | 20/20 | 20/20 |
| `sample_200` | 200/200 | 196/200 |
| `hard1` | 69/69 | 68/69 |
| `hard2` | 200/200 | 197/200 |
| `hard3` | 400/400 | 394/400 |
| `normal` | 1000/1000 | 1000/1000 |
| total | **1889/1889** | 1875/1889 |
| Marathon `normal_100` (canonical manifest) | 100/100, 0 tokens | — |
| Stage 1 evaluation splits (4 × 200, announced Stage 2 categories) | **800/800** | — |

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

## The Omega Institute

This solver is one artifact of the Omega Institute's machine-checked mathematics program. Related
public repositories:

- [Omega-paper-series](https://github.com/the-omega-institute/Omega-paper-series) — the paper series:
  Zeckendorf/Fibonacci combinatorics, symbolic dynamics, folded-rotation certificates, and more, each
  with reproducible scripts and Lean anchors where applicable.
- [newmath](https://github.com/the-omega-institute/newmath) — BEDC (Binary Emission Discovery
  Calculus): a mathlib-free Lean 4 development with first-principles proofs and an autonomous
  paper-deepening pipeline.
- [automath](https://github.com/the-omega-institute/automath) — a continuously running Lean 4
  formalization stream (mathlib-based), source of much of the certificate-engineering experience
  behind this solver.
- [bedc-jepa-gap-ledger](https://github.com/the-omega-institute/bedc-jepa-gap-ledger) — does a world
  model know when it is guessing? A machine-checked gap ledger on real LLM traces.
- [equational_theories](https://github.com/the-omega-institute/equational_theories) — our fork of the
  Equational Theories Project this competition builds on.

- [trureturing](https://github.com/the-omega-institute/trureturing) — the project this solver's
  discipline comes home to: a durable mathematical knowledge base in which a statement is admitted
  only through a kernel-checked Lean proof, recorded in an append-only attestation ledger, and never
  modified in place. The certificate-first rules this solver applies competitively are the same rules
  trureturing applies to lasting mathematical truth.

## Why this solver performs the way it does

The solver's results are the compound interest of the projects above.

- **Lean certificate engineering.** Months of continuous Lean 4 formalization work (the `automath`
  stream and the paper series' Lean anchors) built the working knowledge this solver's certificate
  emitters are made of: which proof shapes the kernel checks in seconds, how far `decide` scales on
  finite structures, and how namespaces interact with a judge's declaration policy.
- **Core-Lean proof discipline.** The BEDC development in `newmath` is deliberately mathlib-free:
  every proof from first principles in core Lean. When the competition's hosted judge moved to a new
  Lean version mid-competition, migrating every certificate family to core-only was routine here —
  version drift in an external library simply has nothing to attach to.
- **Structured-family search.** The countermodel stages search parameterized algebraic families
  (linear, affine, vector-linear, polynomial) with closed-form coefficient checks rather than raw
  enumeration — the same method the paper series applies to combinatorial structures: find the
  parametric family first, then verify inside it in closed form.
- **Measurement discipline.** Every claim carries a machine-checked certificate or a hash-bound
  ledger, and nothing is assumed that has not been measured. That discipline, rather than any single
  algorithm, is what caught the three faults that would each have been fatal in a one-submission
  competition: a prover selection-queue defect, a toolchain migration, and an input-encoding hazard —
  all found by adversarial drills before submission, not after.

## Publication boundary

This repository supports a separate SAIR competition solver paper. It is not
the unified FiberRing + SAIR-EQT2 + FATE-X TMLR/JMLR manuscript and not the FKST
systems paper. Authorship, ordering, target venue, and any post-competition
leaderboard claims remain open until explicitly agreed and evidenced.

The repository remains private before the competition deadline. Creating this
repository, running local validation, or reviewing a pull request does not
submit the solver to SAIR.
