# Final solver review packet (prepared, review not yet requested)

This packet is the single review surface to use after the planned quiet window.
It does not freeze or upload the solver, register a team member, publish the
repository, or request review by itself. At the actual freeze, replace the
candidate commit below with the final head, rerun every command, and request
one review against that exact state.

## Review baseline and current candidate

Israel approved solver v2.2 at commit `b32306d18ab209b3e3a94f88e32e4438cb394d74`
(all four surfaces; eval() ruled acceptable). Final candidate for the single review:

- solver version: **v2.5**; SHA-256 `f2392533c9f4c03b292be80bc6d12e98e5254cc4861d1cc4b227957ad5ed89b4`; 189,504 bytes (limit 500,000).
- branch: `wenlin/v2-merge` (this commit).

## Delta v2.2 -> v2.5 (each step has its own commit trail and regression)

1. **v2.3 — core-only certificates.** The austin_nat family re-emitted without `import Mathlib.Tactic`
   (positive-form replay, `Nat` carrier, core-qualified lemmas). Motivation: the announced hosted judge
   is Lean 4.32; the old certificate needed ~330 s of compilation there (phases of 184 s and 145 s,
   uncomfortably close to the 300 s judge phase cap) and <= 3.1 s after the change. A 120-certificate
   stratified migration corpus covering every emission family compiles 119/120 under exact Lean 4.32.0
   (external attestation; the single non-pass is the legacy pre-rewrite certificate at an external
   120 s-per-phase harness limit, passing at the judge-matching 300 s configuration); every emitted
   family is Lean-core-only.
2. **v2.4 — input encoding + the E168 family.** `_normalize_problem_equations` maps `*` to `◇` at both
   track intakes (the HuggingFace-aligned format uses `*`; the runner feeds the solver verbatim; the
   unpatched solver crashed on every `*`-form problem — measured 0/800 before, 800/800 after). A canned
   exotic order-9 central groupoid settles the E168 goal family (natural central groupoids separate
   none of those goals; the bounded model finder recovers 3/12 at 15x budget).
3. **v2.5 — LLM-fallback overhaul (deterministic definitions unchanged).** Measured defects from a
   hosted run of a stale artifact: returned Lean now normalized `*`->`◇`; prompt states the intro-all-
   goal-variables protocol with a worked example; the hint describes the cascade truthfully and marks
   budget-timeouts as inconclusive; requested directions alternate across the 16 rounds; a raw-Lean
   certificate answer type (infinite carriers allowed) with local size/banned-token validation; and
   countermodel tables are semantically pre-validated (hypothesis holds, goal fails) before any judge
   call, with targeted repair feedback. Definition-level diff confined to: PROMPT, deterministic_hint,
   clean_proof_body, valid_llm_table, main (Pass-3 section), plus new llm_* helpers.
4. **Paper.** Academic-register polish (token-multiset-verified: every number/hash/provenance row
   unchanged); bibliography verified against primary sources (two fabricated author given-names
   corrected, real titles filled, published venues added); Knuth-Bendix / Bachmair-Ganzinger / Austin
   citations added; dual-build (CPP anonymous / arXiv) machinery.

## Evidence at this commit (all clean idle-machine ledgers, judge revision 2848228)

| Surface | Result |
|---|---|
| Solo six public sets | 1889/1889, llm_calls = 0 everywhere |
| Marathon canonical `normal_100` | 100/100, 0 tokens |
| Stage 1 evaluation-distribution drill (4 x 200) | 800/800, full ground-truth agreement |
| Hosted playground (external attestation) | every attempted problem accepted across the four categories (550 attempts incl. the extra-hard tail rerun with the frozen file); the tabulated 200/200 row is evaluation_normal specifically |
| Lean 4.32 migration corpus (external attestation) | 119/120; single non-pass = legacy pre-rewrite certificate at a 120 s-per-phase harness limit, passes at the judge-matching 300 s configuration |
| `check_freeze.py` | PASS |

## Review commands (rerun from a clean clone)

```bash
python3 scripts/check_freeze.py
python3 -m unittest discover -s tests
shasum -a 256 submission/solver.py   # expect f2392533c9f4c03b292be80bc6d12e98e5254cc4861d1cc4b227957ad5ed89b4
```

Uploading to SAIR, publishing the repository, and the arXiv submission remain separate human steps.
