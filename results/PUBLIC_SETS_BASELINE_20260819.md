# Frozen solver on the remaining public sets (local official runner, 2026-08-19)

Solver `submission/solver.py` SHA-256 `ea2946fec56e407382434a4c9ac2b55988de340d0b3c8b7abd7d61d64ed7600a` (frozen baseline). Official judge checkout revision `2848228ff490422442878fd6f5abaf4cfa95257d`, `scripts/setup.sh` rebuilt on this host (Lean v4.30.0-rc2, mathlib `896cc56a`), smoke test passed, sandbox mode `none`, no API key (residuals enter the no-key fallback and fail fast). Local runner scores are not hosted leaderboard results.

| Set | Size | Accepted | LLM calls | Judge calls | Sum of per-item wall-clock | Failed IDs | Ledger SHA-256 |
|---|---:|---:|---:|---:|---:|---|---|
| `hard1` | 69 | 68/69 | 1 | 68 | 511.05 s | `hard1_0062` | `c597a2c20e1aec10a9f2eb87a9c46fb1821d8589cc6b9c7cf07c5b304af72bf0` |
| `hard3` | 400 | 394/400 | 6 | 394 | 2818.74 s | `hard3_0106`, `hard3_0208`, `hard3_0214`, `hard3_0271`, `hard3_0314`, `hard3_0353` | `2c6ee6dbe2a3e614304fcf7e9153e32f0271d4477ce4f53823ccf68a11dba0ba` |
| `normal` | 1000 | 1000/1000 | 0 | 1000 | 2806.79 s | none | `261887f1ffdcadde8f01f869521ed3f6d7b45f3915d260a71f86b8ee7c51944f` |

Together with the archived `sample_20` 20/20, `sample_200` 196/200 and `hard2` 197/200, the frozen solver accepts 1875 of 1889 public-set rows (99.26%). Every accepted row was produced before the LLM fallback and accepted by the official Lean judge. The 14 residuals are 11 true implications (no deterministic proof found within the frozen budgets) and 3 false implications (no countermodel found within the frozen families/carriers).
