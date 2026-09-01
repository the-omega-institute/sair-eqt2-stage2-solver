# FALSE side v2 — Fin-n arithmetic certificates, extended families, Latin model finder, Austin models

Judge facts (official judge rev 2848228, `DEFAULT_PROOF_POLICY`), measured 2026-08-19:

* `decideFin!` is plain `decide`; any arithmetic is allowed inside `submission.*` helpers. So the
  single-digit `finOpTable` limit only binds *table* certificates with n <= 10. For n >= 11 the solver
  emits `def submission.op (x y : Fin n) : Fin n := ⟨<expr> % n, Nat.mod_lt _ (by decide)⟩`
  (closed-form linear / affine / polynomial ops) or packs the table into one Nat literal
  (`def submission.tbl : Nat := …`, lookup `tbl / n ^ (x.val * n + y.val) % n`; kernel Nat
  arithmetic is GMP-accelerated). `docs/SUBSTRATE_NOTES.md`'s "n >= 11 unreachable" is obsolete.
* Judge time is dominated by the number of hypothesis instances n^k (k = #variables of eq1),
  roughly 1 ms per instance: Fin 13 (2 vars) 4 s, Fin 25 (2 vars) 4 s, Fin 43 (2 vars) 5 s,
  Fin 25 (3 vars, 15 625 inst.) 14–16 s, Fin 43 (3 vars, 79 507 inst.) 48 s,
  Fin 50 (3 vars, 125 000 inst.) timed out at 120 s. Packed-table vs closed-form op: same cost
  (the table form costs +1 s at n = 43 and ~3.4 KB). `List.getD` tables cost more and exceed the
  10 KB false-cert cap at n = 50. Hence `FALSE_CERT_MAX_INSTANCES = 60000` clamps every new family
  (n <= 50 for 2-var hypotheses, <= 39 for 3 vars, <= 15 for 4 vars, <= 9 for 5 vars).
* Cert byte cap in `judge/verify.py` is 10 000 (config.json says 20 000); all emitted certs are
  < 10 KB (Austin ℕ certs ~7.7 KB, packed tables <= 4.7 KB at n = 50).

Solver stages touched (`submission/solver.py`, false side only):

1. Stage 1 (`search_counterexample(..., use_structured=True, use_austin=True)`): after the frozen
   brute/linear/F_2^2/Z_n-polynomial families it runs `structured_counterexample(deep=False)`:
   `linear_mod_n` (a x + b y mod n, n = 2..50, exact coefficient check, composite n too),
   `affine_mod_n` (a x + b y + c, (a,b) pruned by the linear part), `vector_linear` over F_3^2 and
   F_2^3 (A x + B y (+c), matrix-linear; F_2^3 scan ~0.6 s with compiled probe checks), then
   `austin_counterexample` (canned ℕ models). Added cost on a TRUE problem ~0.8 s.
2. Stage 3 model finder unchanged in budget (8 s) but `_MFSearch` gained Latin-square propagation:
   `_mf_latin_flags` infers from a law `x = T` (x once in T) which of rows / columns are
   permutations (a step `y ◇ u` with a bare variable y forces every row, `u ◇ y` every column);
   `_assign` rejects duplicates, forces naked singles, and `_choose_cell` uses MRV under the masks.
   hard1_0062 (needs a Fin 8 quasigroup) went from not-found-in-120 s to found in 0.3 s.
3. Stage 5 (new, after `general_true_cert`, before the LLM): `structured_counterexample(deep=True)`
   (quadratic grid n = 7..8, F_5^2 linear, sampled degree <= 3 polynomial ops n <= 16; 60 s cap)
   and the model finder again with 120 s over carriers 4..10.
4. Austin pairs (finite-true, general-false): `_AUSTIN_LAWS` table — ETP 1659-model `f` on ℕ
   (proof text `_AUSTIN_F_LEMMAS`, lemma `f_1659`; `f_2473` via the replayed implication
   `_AUSTIN_F_IMPL`) and its opposite magma for the duals (2000, 1167). Hypothesis matched up to
   variable renaming, goal refuted by `absurd (h a b c) (by decide)` with a witness found on small
   naturals. Covers 148/148 Austin pairs with hypotheses 1659/2000/2473/1167 (witness < 6) of the
   820 listed in ETP `data/Austin_implications.txt`. TODO: the 1661/1979/2481/1133, 2531/1076 and
   1443/1648 families need their own ℕ models (ETP `ManuallyProved/Equation1661.lean` etc.; the 1661
   proof is ~270 lines, over the 10 KB cap unless compressed).

Tooling: `scripts/judge_probe.py <problem.json> <verdict> <cert.lean>` times one certificate on the
official judge; `tests/test_false_side_v2.py` is the offline self-check.
