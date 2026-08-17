# Live gpt-oss-120b run notes (SAIR-EQT2 Stage 2)

Independent execution ledgers for the competition solver, originally run from
the historical `competition/gpt-oss-120b-solver` branch and now archived in
this dedicated repository. These notes describe **fixed-configuration
measurement** of live generation -- not certificate replay.

## Judge / harness

| Item | Value |
|---|---|
| Judge checkout | `equational-theories-lean-stage2` @ `6805e232` |
| Lean toolchain | `leanprover/lean4:v4.30.0-rc2` |
| Official harness | 267-check green (11 suites) before the live runs |
| Submission dir | `/tmp/pilot_submission` containing **only** `solver.py` (Docker sandbox rejects extra files) |

## LLM pin (`pipeline/config.json`)

```json
{
  "model": "openai/gpt-oss-120b",
  "provider": "deepinfra/bf16",
  "max_output_tokens": 65536,
  "temperature": 0.0,
  "reasoning_effort": "medium",
  "use_seed": true,
  "seed": 0
}
```

### Artifact hashes (as run)

| File | sha256 |
|---|---|
| Judge `pipeline/config.json` (as used) | `811c25db11988053d890e23921c5f26109bc99b1c5192b4d6dbdcb22eca711b6` |
| `solver.py` (**pre-fix**, as executed in the live runs) | `22a0bc846288562fbdd63c2f459f2570f50998649816ca4bd0924f68396f1c5e` |

The intro-`G` strip in `clean_proof_body` landed **after** these runs. Live
ledgers were produced with the pre-fix solver hash above.

## Environment deviation

`sandbox.mode` was **`"docker"`** (not the config default `"none"`):

- image: `ee-solver:latest`
- memory: 2048m
- cpus: 2
- pids_limit: 64

## Runs and wall-clock

| Run | Output | Scope | Wall-clock |
|---|---|---|---|
| Pilot 1 | `results/pilot_1_live.json` | `normal_0749` only | ~42 min (2500.6 s) |
| Pilot 2 | `results/pilot_remaining5_live.json` | other 5 residuals | ~4.4 h (15724 s class) |
| Canonical | `results/sample_20_live.json` | full `sample_20.json` | ~5.08 h (18304.0 s) |

Canonical score: **14/20** (deterministic floor); Pass 3 solved **0/6** residuals.

## Cost (OpenRouter credits balance delta)

Measured from OpenRouter `GET /api/v1/credits` balance deltas — **not** from
runner logs.

| Segment | Billed delta |
|---|---|
| Pilots (both) | **$0.1246** |
| Canonical `sample_20` | **$0.1350** |
| Total | **$0.2596** |

### Unavailable telemetry (organizer runner)

The Stage 2 runner stores only a truncated `{response: "<final text>"}` for LLM
turns. The following fields are **unavailable** in these ledgers:

- usage / token counts (including reasoning tokens)
- generation IDs
- raw provider API response bodies

Per the paired v2 requirements framing: do not treat seed pinning as a
substitute for retained event streams when auditing generation.

## Outcome classification notes

- **`normal_0747`**: **INCONCLUSIVE** in both pilot and canonical — hit the
  **3600 s** solver wall-clock around round 13 (not a clean FAILED-after-budget).
- **`normal_0227`**: pilot run **timed out** (~8 LLM rounds / ~3953 s);
  canonical run **completed all 16 rounds** without timeout (~2376 s) and still
  failed.

## Provider nondeterminism (same pin, two runs)

Despite `temperature=0.0` and `seed=0` on the pinned `deepinfra/bf16` route,
**zero** residuals reproduced the same round-1 attempt text across pilot vs
canonical. `normal_0126` additionally **flipped verdict polarity** (pilot FALSE
Fin-2 table vs canonical TRUE/`aesop`).

Keep three notions separate (maintainer terminology):

1. **Fixed-configuration measurement** — same model/provider/token/seed pin,
   same solver bytes, same problems (what these ledgers are).
2. **Nondeterministic generation** — provider-side variance still visible under
   that pin (observed here at round 1).
3. **Certificate replay** — re-checking an already-produced Lean certificate
   through the judge (orthogonal; supported by existing replay-manifest infra).

## Related artifacts in this tree

- Per-round residual diagnostics: `results/DIAGNOSTICS.md`
- Defensive follow-up (not used in the live runs): `clean_proof_body` now strips
  a leading model-reemitted `intro G _ h` because `make_true_code` always
  prepends that binder.
