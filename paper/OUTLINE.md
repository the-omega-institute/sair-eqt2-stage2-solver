# SAIR EQT2 Stage 2 solver paper outline

**Status:** pre-submission outline. No hosted score or final authorship claim.

## 1. Problem and evaluation contract

Describe Stage 2 as proof-producing implication classification over magma
equations. A true verdict requires a Lean proof; a false verdict requires an
explicit countermodel accepted by the same deterministic Lean judge. Separate
local official-runner measurements from hosted competition results.

## 2. Single-file solver architecture

Explain the cheapest-first cascade and why every stage emits a certificate
rather than an unverified label. Record the official single-file, size, time,
model, and judge constraints against an exact upstream revision.

## 3. Countermodel construction

Cover brute small magmas, finite-field and matrix-linear families, polynomial
magmas, and the bounded finite-model search. Explain the `Fin n` table encoding
boundary and how witnesses are independently checked before emission.

## 4. Proof-producing superposition

Describe singleton collapse, substitution instances, and the goal-directed
superposition prover. The contribution is executable certificate construction,
not a new completeness theorem.

## 5. Local official-runner evaluation

Report the 20/20, 196/200, and 197/200 ledgers with exact solver, judge,
config, and ledger hashes. Record their independent reproduction under
official revisions `6805e232` and `2848228`, including the identical failed-ID
sets. State the wall-clock cutoff and local-runner boundaries. Analyze the
seven distinct residual IDs across `sample_200` and `hard2` without tuning
claims from hidden competition data.

## 6. Organizer-model fallback

Report the fixed-configuration `gpt-oss-120b` measurement as a negative result:
0/6 original `sample_20` residuals solved, provider-side nondeterminism despite
temperature 0 and seed 0, and incomplete token telemetry in the runner. Do not
present this as evidence that LLM feedback is generally ineffective.

## 7. Hosted competition result

Reserved until an actual submission is evaluated. Record submission timestamp,
track, exact uploaded solver SHA-256, official score, and public result URL.
Until then this section must say `PENDING` and contain no inferred leaderboard
number.

## 8. Reproducibility and artifact

Document the public release plan after the competition deadline, one-command
structural checks, official upstream pin, Lean toolchain, result ledgers, and
the boundary between the submitted file and development evidence.

## 9. Limitations

Cover public-set tuning risk, wall-clock-sensitive bounded search, absence of a
hosted score before submission, a single competition domain, and the lack of a
formal completeness or performance-superiority claim.
