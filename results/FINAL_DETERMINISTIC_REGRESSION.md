# Final deterministic regression — solver v2.4

Solver `submission/solver.py` SHA-256 `e89cd010b322f77b85099756ce47dcc42a26b45959b2383c7aea9704259ea2a9` (179888 bytes). Official judge revision
`2848228ff490422442878fd6f5abaf4cfa95257d` (`scripts/setup.sh` rerun on the operator host on 2026-08-19; Lean
v4.30.0-rc2, mathlib `896cc56a`; official harness rerun GREEN with zero failures on 2026-08-20; sandbox mode
`none`; no API key). Local official-runner measurements, not hosted leaderboard results.

## Results (2026-08-20, all six public sets; rerun with the v2.4 file, 2026-08-21/22)

| Set | Accepted | LLM calls | Judge calls | Sum of per-item wall-clock | Failed IDs | Ledger |
|---|---:|---:|---:|---:|---|---|
| `sample_20` | 20/20 | 0 | 20 | 68.21 s | none | `results/v2_sample_20_official_2848228.json` (`4a93d4d704f3d76b…`) |
| `sample_200` | 200/200 | 0 | 200 | 893.37 s | none | `results/v2_sample_200_official_2848228.json` (`61a72ebd5f9bb0d4…`) |
| `hard1` | 69/69 | 0 | 69 | 516.61 s | none | `results/v2_hard1_official_2848228.json` (`c2558135fbda9abe…`) |
| `hard2` | 200/200 | 0 | 200 | 1261.27 s | none | `results/v2_hard2_official_2848228.json` (`a2cc9e971c5caeaa…`) |
| `hard3` | 400/400 | 0 | 400 | 2232.47 s | none | `results/v2_hard3_official_2848228.json` (`2e64a5f060a93bdf…`) |
| `normal` | 1000/1000 | 0 | 1000 | 3623.86 s | none | `results/v2_normal_official_2848228.json` (`22b8ed420fdf173d…`) |
| 14 former v1 residuals | 14/14 | 0 | 14 | 131.66 s | none | `results/v2_residuals14_official_2848228.json` |

Totals: **1889/1889 public rows accepted** (v1 frozen baseline: 1875/1889; v2.0 candidate: 1888/1889). Every
accepted row has `llm_calls = 0` and a certificate accepted by the official Lean judge.

Changes from v1 (details in `docs/TRUE_SIDE_G3_PROVER.md` and `docs/FALSE_SIDE_V2_NOTES.md`):

- true side: ordered unit-superposition prover (KBO, forward/backward demodulation with tautology deletion,
  discrimination-tree index, memoised substitution, unifier cache; proof-producing) with anytime deepening
  budgets scaled to the Solo allowance and robust certificate emission; all 11 former true residuals solved,
  `hard3_0314` in under a second of prover time;
- false side: `submission.op` arithmetic certificates for carriers ≥ 11 (judge-validated n = 11…43),
  linear/affine mod n ≤ 50, F_3^2 / F_2^3 vector-linear and polynomial families, Latin-square-propagating
  finite-model search over carriers 4–10, canned ℕ-carrier models for four Austin-pair hypotheses; all 3 former
  false residuals solved;
- stage order: deep false search precedes the deep true pass.

The v2.1 ledgers are the `results/v2_*_official_2848228.json` files bound in `PROVENANCE.json`.

## Marathon track (v2.2)

Same single file, official Marathon runner (`scripts/run_marathon.py`, revision `2848228`), canonical
100-problem manifest, full default budgets: **100/100 accepted, 0 tokens**; fixture `normal_5` 5/5 and the
external-solver Marathon harness 2/2. Evidence: `results/marathon/` (hash-bound in `PROVENANCE.json`).
Solo definitions are unchanged from v2.1 (additive Marathon entry only; `docs/MARATHON_SUPPORT.md`).

## Lean 4.32.0 compatibility (v2.3)

The organizers announced Lean 4.32.0 / Mathlib 4.32.0 as the hosted verification environment
(rules commits `119dbfe`/`e00901b`) while the public harness remains v4.30.0-rc2. A 120-certificate
stratified corpus covering every emission family compiles 120/120 under Lean 4.32.0; v2.3 re-emits
the austin_nat family core-only (positive-form replay, no Mathlib import), taking its 4.32 compile
time from over the judge's 300 s phase cap to ≤ 3.1 s. Every certificate family the solver emits is
now Lean-core-only. The four judge support modules compile unchanged under 4.32.0.

## v2.4: input encoding + the E168 family

- `_normalize_problem_equations` maps `*` to `◇` at both track intakes. The HuggingFace-aligned problem
  format encodes the operator as `*`; normalization previously existed only inside the judge, and the
  runner feeds the solver verbatim, so v2.3 crashed on every `*`-form problem (measured 0/800 before the
  fix on the official Stage 1 evaluation splits).
- `canned_counterexample`: an exotic (non-natural) order-9 central groupoid — natural central groupoids
  satisfy the whole E168 goal family and separate nothing, and the bounded model finder recovers only
  3/12 of the goals even at 15× budget — settles all 12 `evaluation_extra_hard` E168 residuals in one
  `finOpTable` certificate each (~0.1 ms search cost, official runner 12/12 accepted).

## Official-distribution drill (Stage 1 evaluation splits, the announced Stage 2 scoring categories)

| Split | Accepted | Ground-truth agreement |
|---|---:|---|
| `evaluation_normal` | 200/200 | full |
| `evaluation_hard` | 200/200 | full |
| `evaluation_extra_hard` | 200/200 | full |
| `evaluation_order5` | 200/200 | full |

**800/800** with `llm_calls = 0` on every accepted row (`results/official_distribution_drill/`,
hash-bound in `PROVENANCE.json`). Stage 2 will not reuse these problems; this measures readiness on the
announced scoring distribution, not a hosted score. Separately, the hosted Stage 2 playground accepted
100/100 on its first 100 problems (official infrastructure, Lean 4.32 toolchain; recorded in
`PROVENANCE.json`).

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
