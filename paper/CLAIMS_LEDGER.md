# Competition paper claims ledger

This file is the maximum current claim surface. Manuscript prose may be weaker,
but not stronger, until new durable evidence is added.

## Supported now

- The frozen solver emits Lean-checkable proof or countermodel certificates and
  relies on the official judge for acceptance.
- The archived local official-runner regressions record 20/20 on `sample_20`,
  196/200 on `sample_200`, and 197/200 on `hard2` for solver SHA-256
  `ea2946fec56e407382434a4c9ac2b55988de340d0b3c8b7abd7d61d64ed7600a`.
- Every accepted row in those three ledgers was solved before the LLM fallback.
- A separate pre-optimization live measurement of organizer-pinned
  `gpt-oss-120b` solved 0/6 original `sample_20` residuals.
- The live model generated different first attempts under the same advertised
  temperature and seed configuration; this is an observed provider behavior,
  not a proof of universal nondeterminism.

## Not supported yet

- No hosted leaderboard score or rank.
- No claim that the local public-set result transfers to hidden evaluation.
- No claim that the bounded search is deterministic across machine load.
- No completeness theorem for the countermodel or superposition procedures.
- No general claim that LLM feedback is ineffective.
- No comparative superiority over other competition solvers.
- No final authorship, author order, venue, or paper-submission claim.
