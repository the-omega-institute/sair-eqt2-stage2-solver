# Lean 4.32 certificate compatibility audit

Date: 2026-08-20 (Asia/Singapore)

## Outcome

Two stages are recorded in this directory.

**Preflight (blocked).** The first attempt was blocked before compilation in a
managed workspace: `leanprover/lean4:v4.32.0` was not installed and Elan/curl
were denied network access (`results.json`). That stage made no claim that the
certificates pass Lean 4.32.0.

**Exact run (completed).** The exact Lean 4.32.0 + Mathlib v4.32.0 run was
subsequently completed on the operator host (`results-exact-4.32.json`):
119/120 certificates pass under the harness's 120 s per-phase limit. The single
non-pass is the legacy pre-v2.3 Mathlib-importing Austin certificate
(`hard2_0027`), whose problem phase timed out at 120 s; under a 300 s-per-phase
configuration matching the judge it passes (phases 183.6 s and 144.6 s, total
330.5 s — `results-retry-hard2_0027.json`). The corpus characterizes the
migration-era certificate set, not the frozen v2.5 artifact's current output:
the frozen solver's own certificate for the same problem imports only
`JudgeProblem` and is accepted in 4.93 s
(`results/lean4331_revalidation/hard2.json`). These runs executed outside the
repository and are recorded as external operator attestations.

All work that does not require the missing executable is complete. The project,
exact Mathlib lock, byte-identical judge modules, verify-compatible driver, and
120-row corpus are ready. As a bounded forward proxy, the unchanged core judge
modules and 119 core-only certificates were compiled under the locally available
Lean 4.33.0-rc1. All 119 passed after serial retry of three load-induced
timeouts. The sole Mathlib-dependent certificate was not testable in that
core-only proxy.

Exact preflight details are in `results.json`; proxy details are in
`results-proxy-4.33-merged.json`.

## Setup decisions

- `lean-toolchain` is exactly `leanprover/lean4:v4.32.0`.
- Mathlib is pinned to the official `v4.32.0` release, commit
  `81a5d257c8e410db227a6665ed08f64fea08e997`. The release exists, so the
  plain-Lean fallback was **not** selected. The release listing is at
  <https://github.com/leanprover-community/mathlib4/releases/tag/v4.32.0>.
- `lake-manifest.json` locks Mathlib and all eight transitive package revisions
  recorded by Mathlib v4.32.0.
- `lake exe cache get` was attempted. Elan could not start Lake because it first
  needed to download Lean 4.32.0 and DNS resolution of `github.com` is disabled.
- The four judge modules import only core (`Lean`) or one another. Mathlib is
  nevertheless required by corpus row `hard2_0027`, which imports
  `Mathlib.Tactic` and uses `omega`, `simp`, and `grind`.
- `git init` was attempted as requested, but the managed filesystem gives the
  root `.git` path a read-only policy and returned `Operation not permitted`.
  No protected checkout was modified.

## Judge-module migration signals

The copied files are byte-for-byte identical to the organizer checkout:

| Module | SHA-256 | Copy differs? |
|---|---|---:|
| `JudgeMagma/Magma.lean` | `8bc1d23fd58f993297b246454e9fa97f97c69494783ddd3e04b9075c34c3bab4` | No |
| `JudgeDecide/DecideBang.lean` | `4b83154198d442d41366abfa8d09fea44016aaf6f8eb6a5dae55aadcbed5915f` | No |
| `JudgeFinOp/MemoFinOp.lean` | `7ae1c13a209893a6f3cc4c52cd784cdc4cf70660fb5cfe3db7b9ff58a3006f18` | No |
| `JudgeSupport/Inspect.lean` | `02317cd7beb7a3c2a62c093ef97829b9a78e4e902aa181cd446665db0c42d174` | No |

Lean 4.33.0-rc1 compiled all four unchanged. This is useful forward evidence,
but it is not a substitute for compiling them under 4.32.0. Therefore the exact
4.32 organizer-side migration edit count is **unknown**, not zero. No edits have
been made that could conceal a migration signal.

## Driver fidelity

`scripts/verify_corpus.py` performs, per row:

1. Normalize `*` to `◇`, derive binders from the equation strings, and compile
   `JudgeProblem.lean`.
2. Use the verbatim goal forms from `verify.py`:
   - true: `∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G`
   - false: `∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G`
3. Compile the certificate verbatim as `Submission.lean`.
4. Compile/run the judge-controlled `Problem.lean` containing
   `example : Goal := submission` and `#judge_report submission ...`.
5. Preserve per-phase timings, stdout/stderr, axioms, direct declarations,
   artifact path, and family labels in JSON.

The default is the exact Lake project. `--direct-support` exists only for the
explicitly labeled, Mathlib-free proxy run.

## Corpus

`scripts/prepare_corpus.py` joined accepted solver rows to organizer problem
strings by `id`, checked any result-side equation IDs, and emitted
`corpus/sample_120.json` (SHA-256
`ed7eb39fa7eda8b6739d056dbb669be21c79ef1f1f3027e12bbe8d3309168b2c`).

- 1,969 accepted source rows were considered after canonicalizing overlapping
  v2 outputs while retaining marathon provenance separately.
- Exactly 120 were selected.
- All 14 certificates from `v2_residuals14_official_2848228.json` are present.
- Ten rows retain direct `marathon/normal_100_answers.jsonl` provenance.
- Families are intentionally overlapping; a `finOpTable` certificate also
  counts as `decideFin_usage`.
- The accepted inputs contain only one unique `grind`-bearing certificate,
  `hard2_0027`. It also supplies the Nat/infinite-carrier, `austin_nat`, and
  generated eq-lemma/rw/grind replay coverage. There is no standalone accepted
  true G3 pool certificate in the requested result files.
- The longest sampled replay is residual `hard3_0314`: 9,380 source characters,
  41 `have`s, and 38 `congrArg`s.

## Per-family results

Exact Lean 4.32.0 results are all **not run** because the executable preflight
failed. The table below reports the clearly labeled Lean 4.33.0-rc1 core-only
proxy after serial retry. Its one failure is an unavailable import, not a Lean
rejection of the proof.

| Family | Sample | Proxy pass | Proxy fail | Exact 4.32 |
|---|---:|---:|---:|---:|
| finOpTable false | 30 | 30 | 0 | not run |
| arithmetic `submission.op` false, n≥11 | 1 | 1 | 0 | not run |
| Nat / infinite-carrier false | 1 | 0 | 1 infra | not run |
| `austin_nat` | 1 | 0 | 1 infra | not run |
| `decideFin!` usage | 31 | 31 | 0 | not run |
| singleton simple true | 18 | 18 | 0 | not run |
| substitution-instance true | 18 | 18 | 0 | not run |
| singleton superposition true | 8 | 8 | 0 | not run |
| short superposition replay | 24 | 24 | 0 | not run |
| long superposition replay | 28 | 28 | 0 | not run |
| `congrArg` chains | 52 | 52 | 0 | not run |
| lemma-pool/rw + `grind` signature | 1 | 0 | 1 infra | not run |
| any `grind` | 1 | 0 | 1 infra | not run |
| **Overall rows** | **120** | **119** | **1 infra** | **not run** |

## Failures and diagnosis

### Exact Lean 4.32.0

There are no certificate-level results to diagnose. Compilation never started.
The preflight errors were:

```text
$ lake --version
error: error during download
info: caused by: [6] Couldn't resolve host name (Could not resolve host: github.com)

$ lake exe cache get
error: error during download
info: caused by: [6] Couldn't resolve host name (Could not resolve host: github.com)
```

This is an execution-environment/toolchain availability failure, not tactic or
API breakage.

### Lean 4.33.0-rc1 proxy

One row failed:

- `hard2_0027` (residual; Nat/austin/lemma-pool/grind families), submission
  phase:

  ```text
  Submission.lean:1:0: error: unknown module prefix 'Mathlib'
  No directory 'Mathlib' or file 'Mathlib.olean' in the search path entries
  ```

  Diagnosis: intentional proxy infrastructure limitation. It does not show a
  tactic rename, `grind` behavior change, deprecated API, or proof defect.

Three `decideFin!` rows (`hard1_0062`, `hard2_0009`, `hard1_0024`) initially
timed out at 120 seconds while four Lean jobs competed for CPU. All passed when
rerun serially at the unchanged 120-second per-phase limit:

| ID | Fin n | Submission | Whole row |
|---|---:|---:|---:|
| `hard1_0062` | 8 | 31.833 s | 54.970 s |
| `hard2_0009` | 8 | 42.940 s | 58.449 s |
| `hard1_0024` | 9 | 54.279 s | 70.698 s |

Diagnosis: host contention, not a persistent decide failure. Exact 4.32 should
still be run serially (or with one compiler per physical CPU budget) before
making a performance claim.

## Solver emission recommendations

No solver emission change is justified by the evidence available so far. Every
core-only family, including the longest `congrArg` replay and `Fin 13`
arithmetic witness, survives the newer 4.33.0-rc1 proxy unchanged.

Do not change `austin_nat`, `omega`, or `grind` emission based on the proxy's
missing-Mathlib error. If the exact run later rejects `hard2_0027`, use that
actual diagnostic to choose the smallest change; likely branches would be a
tactic import/API adjustment or a local proof rewrite, but neither is presently
evidenced.

For performance only, the test runner should avoid oversubscribing
`decideFin!` compilations. This is a harness/concurrency recommendation, not a
solver-code change.

## Completing the exact run

Once Lean 4.32.0 can be installed or made available on `PATH`, run from this
directory:

```bash
elan toolchain install leanprover/lean4:v4.32.0
lake update
lake exe cache get
python3 scripts/verify_corpus.py \
  --input corpus/sample_120.json \
  --output results-exact-4.32.json \
  --artifacts artifacts-exact-4.32 \
  --jobs 1 \
  --timeout 120
```

Use `--jobs 1` for the first measurement because the proxy demonstrated
contention sensitivity. A completed exact run can then replace the blocked
entry in `results.json` and supply the requested definitive migration and
solver recommendations.
