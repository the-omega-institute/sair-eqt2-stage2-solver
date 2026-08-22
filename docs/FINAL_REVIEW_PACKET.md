# Final solver review packet (prepared, review not yet requested)

This packet is the single review surface to use after the planned quiet window.
It does not freeze or upload the solver, register a team member, publish the
repository, or request review by itself. At the actual freeze, replace the
candidate commit below with the final head, rerun every command, and request
one review against that exact state.

## Review baseline and current candidate

Israel approved solver v2.2 at commit `b32306d18ab209b3e3a94f88e32e4438cb394d74`:

- SHA-256 `931b08812ecae603dfa80e82c214d193c3ec8f82d703ab06a8edc3bdddef4697`;
- 178,769 bytes;
- Solo 1889/1889 and Marathon `normal_100` 100/100;
- single-file Solo contract and official Marathon I/O contract accepted;
- evidence/provenance and claims boundary accepted.

Current prepared candidate:

- branch head at packet preparation: `feebfbba024b2b74c87d88a85813cc2f82630c20`;
- solver version: v2.4;
- SHA-256 `e89cd010b322f77b85099756ce47dcc42a26b45959b2383c7aea9704259ea2a9`;
- 179,888 bytes, below the 500,000-byte limit.

The head commit is expected to advance for documentation only. The final
review must bind the then-current commit and independently recheck that the
solver SHA-256 and byte count remain exactly the values above. Any solver-byte
change invalidates this packet and requires regenerated evidence.

## Complete solver delta since approved v2.2

The solver diff from `b32306d` to v2.4 is 71 insertions and 31 deletions,
confined to three bounded changes:

1. **Lean-core-only Austin certificates (v2.3).** The Austin `Nat` emitter no
   longer imports `Mathlib.Tactic`. It uses positive-form replay, core-qualified
   names, and `import JudgeProblem` only. This closes the observed Lean 4.32
   timeout caused by Mathlib elaboration; all four variants compile in at most
   3.1 seconds under Lean 4.32 core.
2. **Problem-encoding normalization (v2.4).** Both Solo and Marathon intake map
   `*` to `◇`, matching the official judge's equation normalization. The
   published HuggingFace-aligned data uses `*`; v2.3 otherwise failed before
   parsing every row in the 800-problem distribution drill.
3. **E168-family countermodel (v2.4).** A fixed exotic order-9 central groupoid
   is checked by the existing equation evaluator before use and emitted through
   the existing `finOpTable` certificate path. It settles the 12 E168-family
   residuals in `evaluation_extra_hard`; the official judge accepted all 12.

No LLM prompt, key handling, Solo protocol, Marathon I/O contract, judge
protocol, or external dependency was added or relaxed by these changes.

## Evidence bound to the current solver

- Structural freeze check: `python3 scripts/check_freeze.py` passes.
- Repository unit tests: 8/8 pass.
- Local official runner at revision `2848228`: 1889/1889 over all six public
  sets, with `llm_calls = 0` on every accepted row.
- Local official Marathon runner: canonical `normal_100` is 100/100 with
  0 tokens.
- Published Stage 1 evaluation splits: 800/800 with full ground-truth
  agreement and 0 LLM calls.
- Lean 4.32 compatibility corpus: 120/120 certificates compile; every emitted
  certificate family is Lean-core-only.
- Hosted Stage 2 playground: the same v2.4-candidate file was accepted on all
  200 `evaluation_normal` problems, with 0 rejected, 0 errors, and 0 LLM calls.

`PROVENANCE.json` binds the solver, official revision/configuration, local
ledgers, Marathon artifacts, distribution-drill ledgers, Lean 4.32 record, and
hosted playground measurement. The playground result is not a formal
submission, leaderboard score, rank, or hidden-set transfer result.

## Four review surfaces

1. **Frozen solver bytes:** independently verify the final commit, SHA-256,
   byte count, and that `submission/` contains only `solver.py`.
2. **Rules and harness compliance:** confirm the Solo single-file boundary,
   official Marathon manifest/output access, no key or repository reads on the
   Solo path, no shell-out/network client, and judge/LLM calls only through the
   official protocol.
3. **Evidence traceability:** run `scripts/check_freeze.py`, inspect
   `PROVENANCE.json`, and confirm every claimed count is backed by the named
   hash-bound ledger or hosted measurement record.
4. **Scientific claim boundary:** confirm `paper/CLAIMS_LEDGER.md` does not
   infer a leaderboard score, rank, hidden-set transfer, completeness,
   cross-machine determinism, or comparative superiority.

## Final freeze commands

```bash
git diff b32306d18ab209b3e3a94f88e32e4438cb394d74..HEAD -- submission/solver.py
shasum -a 256 submission/solver.py
wc -c submission/solver.py
PYTHONDONTWRITEBYTECODE=1 python3 scripts/check_freeze.py
PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover -s tests -v
```

After those checks and green CI, request one final review against the exact
head. Team registration, solver upload, hosted submission, repository
publication, and paper authorship/order remain separate human decisions.
