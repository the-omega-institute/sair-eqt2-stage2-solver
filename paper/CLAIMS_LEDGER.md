# Competition paper claims ledger

This file is the maximum current claim surface. Manuscript prose may be weaker,
but not stronger, until new durable evidence is added.

## Supported now

- The frozen solver emits Lean-checkable proof or countermodel certificates and
  relies on the official judge for acceptance.
- Solver v2.4 (SHA-256 `e89cd010b322f77b85099756ce47dcc42a26b45959b2383c7aea9704259ea2a9`,
  179,888 bytes) records 20/20 `sample_20`, 200/200 `sample_200`, 69/69 `hard1`,
  200/200 `hard2`, 400/400 `hard3`, 1000/1000 `normal` — **1889/1889 public
  rows** — in archived local official-runner ledgers under official revision
  `2848228`; the complete `2848228` official harness passed with zero failures
  on the same host on 2026-08-20. The same file passes the official Marathon runner on the canonical `normal_100` manifest with 100/100 accepted and 0 tokens (local measurement). A 120-certificate stratified corpus covering every emission family compiles 120/120 under Lean 4.32.0, the announced hosted verification environment; every emitted certificate family is Lean-core-only. The solver accepts both `◇` and `*` problem encodings. On the four Stage 1 evaluation splits (the announced Stage 2 scoring categories) it records 800/800 with full ground-truth agreement (local measurement); the same v2.4-candidate file was also accepted on all 200 `evaluation_normal` problems in the hosted Stage 2 playground, with 0 rejected, 0 errors, and 0 LLM calls. The playground measurement is not a leaderboard score.
- The superseded v1 solver (`ea2946fe…`) recorded 20/20, 196/200 and 197/200
  on `sample_20`/`sample_200`/`hard2`, reproduced identically under `6805e232`
  and `2848228`, and 68/69, 394/400, 1000/1000 on `hard1`/`hard3`/`normal`
  (1875/1889); the 14 v1 residuals are exactly the rows v2 newly solves plus
  `hard3_0314`.
- Every accepted row in every archived ledger was solved before the LLM
  fallback (`llm_calls = 0`).
- Countermodels on carriers `Fin n`, n ≥ 11, are certifiable through an
  operation defined inside the `submission` namespace; this was validated on the
  official judge for n = 11, 13, 16, 25, 43.
- A separate pre-optimization live measurement of organizer-pinned
  `gpt-oss-120b` solved 0/6 original `sample_20` residuals.
- The live model generated different first attempts under the same advertised
  temperature and seed configuration; this is an observed provider behavior,
  not a proof of universal nondeterminism.

## Not supported yet

- No hosted leaderboard score or rank.
- No claim that the local public-set result transfers to hidden evaluation.
- No claim that the bounded search is deterministic across machine load
  (v2's deep stages are time-budgeted; results under heavier load may differ).
- No completeness theorem for the countermodel or superposition procedures.
- No general claim that LLM feedback is ineffective.
- No comparative superiority over other competition solvers.
- No final authorship, author order, venue, or paper-submission claim.
