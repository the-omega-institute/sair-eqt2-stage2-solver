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
