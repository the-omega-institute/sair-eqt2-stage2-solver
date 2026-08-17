# Latest-upstream deterministic regression

This replay validates the frozen solver against official SAIR EQT2 Stage 2
revision `2848228ff490422442878fd6f5abaf4cfa95257d`. These are local official-
runner measurements, not hosted leaderboard results.

## Frozen inputs

| Input | Value |
|---|---|
| Official revision | `2848228ff490422442878fd6f5abaf4cfa95257d` |
| Runner config SHA-256 | `82aca7ad4709cf57f67979aeed0e954bd17ddeacc3c2d9dc70e2130e1d44300b` |
| Lean toolchain | `leanprover/lean4:v4.30.0-rc2` |
| Solver SHA-256 | `ea2946fec56e407382434a4c9ac2b55988de340d0b3c8b7abd7d61d64ed7600a` |
| Solver size | 82,370 bytes |
| Run date | 2026-08-17 |

The complete official harness was green with zero failures before these runs:
68/68 judge cases, 32/32 judge internals, 24/24 banned-token checks, 55/55
pipeline checks, 4/4 repeatability checks, 3/3 verify-branch checks, 79/79
public challenger attacks, 4/4 infrastructure attacks, 7/7 loader checks,
11/11 submit-CLI checks, and 1/1 README consistency check.

## Results

| Set | Accepted | LLM calls | Judge calls | Sum of per-item wall-clock | Failed IDs |
|---|---:|---:|---:|---:|---|
| `sample_20` | 20/20 | 0 | 20 | 57.20 s | none |
| `sample_200` | 196/200 | 4 | 196 | 1011.55 s | `true_2860_3458`, `true_2135_2128`, `true_2055_2656`, `true_1636_1839` |
| `hard2` | 197/200 | 3 | 197 | 1538.14 s | `hard2_0027`, `hard2_0051`, `hard2_0178` |

Every accepted row was solved before the LLM fallback and accepted by the
official Lean judge. Each failed row made one no-key fallback request, which
returned an environment error and produced no candidate certificate.

The scores and failed-ID sets match the earlier complete regression under
official revision `6805e232` exactly. This demonstrates replay stability for
these public sets across the two pinned revisions. It does not establish a
hosted score or transfer to the hidden evaluation set.

## Ledgers

- `sample_20_official_2848228.json` (SHA-256 `33ad4b699eb5297e25132ff9ac2c01c4657ec61bcb62a9a918232e380ffdb177`)
- `sample_200_official_2848228.json` (SHA-256 `b7f47a2d36086f3fd58f792f6bcc5ffbbd57bc0a5e945206a0a881b5bde7c283`)
- `hard2_official_2848228.json` (SHA-256 `631f35621b265f2fa58a597b341859a7c31b6f2fa79b752fb039e0c420f39fba`)
