# Competition paper claims ledger

This file is the maximum current claim surface. Manuscript prose may be weaker,
but not stronger, until new durable evidence is added.

## Supported now

- The frozen solver emits Lean-checkable proof or countermodel certificates and
  relies on the official judge for acceptance.
- Solver v2.5 (SHA-256 `f2392533c9f4c03b292be80bc6d12e98e5254cc4861d1cc4b227957ad5ed89b4`,
  189,504 bytes) records 20/20 `sample_20`, 200/200 `sample_200`, 69/69 `hard1`,
  200/200 `hard2`, 400/400 `hard3`, 1000/1000 `normal` — **1889/1889 public
  rows** — in archived local official-runner ledgers under official revision
  `2848228`; the complete `2848228` official harness passed with zero failures
  on the same host on 2026-08-20. The same file passes the official Marathon runner on the canonical `normal_100` manifest with 100/100 accepted and 0 tokens (local measurement). A 120-certificate stratified corpus covering every emission family compiled 119/120 in the exact external Lean 4.32.0 + Mathlib run (archived, hash-bound, in results/lean432_corpus/; the one non-pass was the pre-v2.3 Austin certificate at the judge phase limit, which motivated the core-only rewrite) — an external operator attestation; every emitted certificate family is Lean-core-only. The solver accepts both `◇` and `*` problem encodings. On the four Stage 1 evaluation splits (the announced Stage 2 scoring categories) it records 800/800 with full ground-truth agreement (local measurement); the hosted Stage 2 playground runs are external operator attestations (no committable ledger exists): across the four categories every attempted problem was accepted with zero LLM calls, including a rerun of the extra-hard tail with the frozen v2.5 file. The repository-verifiable evidence for the same material is the committed Solo/Marathon/drill ledgers and the Lean 4.33.1 revalidation.
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

- On the official `stage2_stress_test` set (announced as mirroring the final leaderboard
  configuration), the frozen v2.5 solver records 200/200 with zero LLM calls and full ground-truth
  agreement (committed ledger `results/stage2_stress_test_results.json`). On the research-tier
  `research_order5_hard` set (not scored; ground truth partly unknown; Austin-law false directions
  admit no finite countermodels) it certifies 0/100 within budget — recorded as an honest negative
  (`results/research_order5_hard_attempt.json`).

## Not supported yet

- No hosted leaderboard score or rank.
- No claim that the local public-set result transfers to hidden evaluation.
- No claim that the bounded search is deterministic across machine load
  (v2's deep stages are time-budgeted; results under heavier load may differ).
- No completeness theorem for the countermodel or superposition procedures.
- No general claim that LLM feedback is ineffective.
- No comparative superiority over other competition solvers.
- No final authorship, author order, venue, or paper-submission claim.
