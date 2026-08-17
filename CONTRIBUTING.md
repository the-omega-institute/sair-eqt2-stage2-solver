# Contributing

Use pull requests for solver, evidence, and manuscript changes. Keep the
following boundaries explicit in every review:

- `submission/` must contain only `solver.py`.
- Any score change requires an archived full runner ledger and exact solver,
  judge, and config hashes.
- Local official-runner measurements are not leaderboard results.
- A certificate counts as accepted only when the official Lean judge accepts
  it; generated text alone is not a result.
- Never commit API keys, provider responses containing credentials, private
  competition data, or unredacted account information.
- Do not change authorship, submit to the competition, publish the repository,
  or submit a paper through a code review.

The main review surfaces for Israel are the frozen solver bytes, rule and
harness compliance, result/provenance traceability, and the scientific claim
boundary for the competition paper.
