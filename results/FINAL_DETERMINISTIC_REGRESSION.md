# Final deterministic regression — solver v2

Solver `submission/solver.py` SHA-256 `29ba1ec88c87fe051afd3f8bf007b2b9b8efa415e33597faba6d4df9fa07e36c` (160448 bytes). Official judge revision
`2848228ff490422442878fd6f5abaf4cfa95257d` (`scripts/setup.sh` rerun on the operator host on 2026-08-19; Lean
v4.30.0-rc2, mathlib `896cc56a`; smoke test passed; sandbox mode `none`; no API key, so any residual enters the
no-key fallback and fails fast). Local official-runner measurements, not hosted leaderboard results.

## Results (2026-08-19/20, all six public sets)

| Set | Accepted | LLM calls | Judge calls | Sum of per-item wall-clock | Failed IDs | Ledger |
|---|---:|---:|---:|---:|---|---|
| `sample_20` | 20/20 | 0 | 20 | 68.69 s | none | `results/v2_sample_20_official_2848228.json` (`3ba53957f6e4045e…`) |
| `sample_200` | 200/200 | 0 | 200 | 893.81 s | none | `results/v2_sample_200_official_2848228.json` (`d0bb6816ea04ede1…`) |
| `hard1` | 69/69 | 0 | 69 | 512.2 s | none | `results/v2_hard1_official_2848228.json` (`64ae26489fbd2051…`) |
| `hard2` | 200/200 | 0 | 200 | 1251.8 s | none | `results/v2_hard2_official_2848228.json` (`a3e5cbc1dc692351…`) |
| `hard3` | 399/400 | 1 | 400 | 2990.83 s | `hard3_0314` | `results/v2_hard3_official_2848228.json` (`5d46327265fa8a97…`) |
| `normal` | 1000/1000 | 0 | 1000 | 3567.34 s | none | `results/v2_normal_official_2848228.json` (`2b2f8f15f1a6a0cd…`) |
| 14 former residuals | 13/14 | 1 | 14 | 929.1 s | `hard3_0314` | `results/v2_residuals14_official_2848228.json` |

Totals: **1888/1889 public rows accepted** (v1 frozen baseline: 1875/1889). Every accepted row has `llm_calls = 0`
and a certificate accepted by the official Lean judge. The single failed row `hard3_0314` (2923 ⇒ 1623) needs a
long superposition derivation that the in-file prover does not reach within its budget.

What changed from v1 (details in `docs/TRUE_SIDE_G3_PROVER.md` and `docs/FALSE_SIDE_V2_NOTES.md`):

- true side: new ordered unit-superposition prover (KBO, demodulation, indexed, proof-producing) with anytime
  budgets scaled to the Solo allowance and robust certificate emission; 10 of the 11 former true residuals solved;
- false side: Fin-n arithmetic certificates through `submission.op` (carriers 11–43 validated on the judge),
  linear/affine mod n ≤ 50, F_3^2 / F_2^3 vector-linear and polynomial families, Latin-square-propagating finite
  model search over carriers 4–10, and canned ℕ-carrier models for four Austin-pair hypotheses; all 3 former false
  residuals solved;
- stage order: deep false search now precedes the deep true pass.

The v2 ledgers are the `results/v2_*_official_2848228.json` files bound in `PROVENANCE.json`.

---

# Superseded v1 baseline (solver `ea2946fe…`, retained for history)

# Final deterministic regression

This regression measures the competition solver after the proof-producing
finite-model and superposition stages were added and after PR #7 was merged.
It uses the official Stage 2 runner and Lean judge. These are local-runner
measurements, not hosted-leaderboard scores.

## Frozen inputs

| Input | Value |
|---|---|
| Judge checkout | `6805e2323018fbd8a85f41ca09fc33d74d5a02a5` |
| Judge config SHA-256 | `82aca7ad4709cf57f67979aeed0e954bd17ddeacc3c2d9dc70e2130e1d44300b` |
| Solver SHA-256 | `ea2946fec56e407382434a4c9ac2b55988de340d0b3c8b7abd7d61d64ed7600a` |
| Solver size | 82,370 bytes |

## Results

| Set | Accepted | LLM calls | Judge calls | Sum of per-item wall-clock | Failed IDs |
|---|---:|---:|---:|---:|---|
| `sample_20` | 20/20 | 0 | 20 | 41.10 s | none |
| `sample_200` | 196/200 | 4 | 196 | 999.38 s | `true_2860_3458`, `true_2135_2128`, `true_2055_2656`, `true_1636_1839` |
| `hard2` | 197/200 | 3 | 197 | 1352.89 s | `hard2_0027`, `hard2_0051`, `hard2_0178` |

Every accepted row was produced before the LLM fallback (`llm_calls = 0` for
that row) and was accepted by the official Lean judge. The aggregate LLM calls
above are the failed residuals entering the no-key fallback; no model response
or certificate was produced in this regression.

The archived evidence for this regression is the three ledgers below. A
separate unarchived run recorded `hard2` 196/200, but no ledger, timing data, or
load telemetry survives for that run, so the cause of the one-item difference
is not established. The durable result is the archived 197/200 observation;
the unarchived 196/200 observation must be labeled as such wherever mentioned.

## Related targeted replay

`general66_provenance_ledger.json` records a separate targeted replay of the 66
non-singleton TRUE residuals. It verifies 61/66 under solver SHA-256
`0b1c5008eb52942afd03ad34c45ef1b6ce4f54d8e376d84e26e605a82f253294`.
The current solver and the three full-set regression ledgers use SHA-256
`ea2946fec56e407382434a4c9ac2b55988de340d0b3c8b7abd7d61d64ed7600a`.

The two solver files differ only in PR #7's five-line `clean_proof_body`
change on the LLM path; their deterministic stages are unchanged. This makes
the targeted replay valid evidence for the 61/66 component attribution, but it
is not a byte-identical replay of the current solver. Such a confirmation would
require rerunning those 66 items under `ea2946fe...`.

## Ledgers

- `sample_20_deterministic_final.json` (SHA-256 `f6c8732807758486be94c0cedadfca317e2221308a355fb8b4c944a3e1fab819`)
- `sample_200_deterministic_final.json` (SHA-256 `46260ef51cf3a600dad091a93c9498a87c71025e6174dde9f80b5c73ae9d3490`)
- `hard2_deterministic_final.json` (SHA-256 `448d3ff415e3e23901815b81a3713f0ccea694490986e0d04d18ab7b1eeb568c`)
- `general66_provenance_ledger.json` is the separate targeted replay described
  above and intentionally retains its executed solver hash `0b1c5008...`.

Re-run from the pinned official judge checkout after loading `.env.judge`:

```sh
PYTHONDONTWRITEBYTECODE=1 .venv/bin/python -m pipeline.runner \
  --submission /path/to/submission-only-dir \
  --problems examples/problems/sample_200.json \
  --output /path/to/sample_200_deterministic_final.json
```

The submission directory must contain only `solver.py`; the Docker sandbox
rejects development files placed beside the submission.
