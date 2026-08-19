# TRUE side: G3 ordered-superposition prover (branch wenlin/v2-true)

Scope of this change: true-side stages of `submission/solver.py` only
(`general_true_cert`, new `g3_*`/`_G3*` block, the true-side lines of `main()`).
False-side stages are untouched.

## What changed

1. Budgets (Solo: `budget.timeout_seconds` = 3600 read from the startup message)
   - Stage 2c (new): quick G3 pass, `min(6, max(1, wall/600))` s (6 s in Solo),
     placed before the model finder because it settles essentially every
     provable implication in well under a second.
   - Stage 4: deep anytime G3 pass, `min(600, max(20, wall/6))` s (600 s in
     Solo, 50 s at a 300 s Marathon-style allowance), iterative size-cap
     deepening `[(24, 8%), (32, 17%), (44, 30%), (60, rest)]`; the final
     round switches to the Vampire-like selection (`var_penalty=0`,
     `age_ratio=2`). `_g2_search` (old goal-joining prover) keeps a 15 %
     slice as diversity fallback.
   - Rejected exact certificate -> robust re-emission (`first | exact _ | grind`
     per step, final `grind` fallback), no re-search.
   - Stage 4b (new): lemma-pool + `grind` certificate from the failed search
     (40 smallest derived lemmas, exact proofs, then `grind`). One judge call.

2. Prover (`_G3Prover`): unit-equational ordered superposition / unfailing
   completion with a negated, Skolemised goal clause.
   - KBO (unit weights, single symbol) orients equations; inferences only
     from/into maximal sides, post-unification ordering checks.
   - Forward demodulation of every generated equation (innermost, cached
     normal forms versioned by rule set), backward demodulation of the active
     set by each new oriented rule, variant dedup via hashed symmetric
     alpha-keys, size/variable caps.
   - Discrimination-tree (linear skeleton) index for demodulation candidates.
   - Given-clause selection: weight + var penalty heap interleaved with an age
     queue (`age_ratio`).
   - Goal: negative clause `u != v` over Skolem constants; superposition of
     active rules into it (both sides, ordering restricted), demodulation,
     refutation by unification; steps recorded for replay.
   - Passive queue stores *recipes* (source, target, direction, path) instead
     of equations; the full proof object is rebuilt on selection. 250k
     passive entries ~ 220 MB (was 2.2 GB).
   - Emission: exact positive-form certificate (`have eN (X0 .. : G) : l = r :=
     by exact (congrArg (fun q => C[q]) (eM args)).symm.trans (eK args)`, goal
     steps `gI`, final `.trans` chain) -- the same shape as the frozen `_g2`
     emitter, allow-list clean.

## Measurements (official judge rev 2848228, `pipeline.runner`, no API key)

Residuals (11 TRUE residuals of the frozen solver): 10/11 solved, each in
4.5-7 s wall (including ~2.5 s runner/Lean overhead); `hard3_0314`
(2923 => 1623) still fails after the full 600 s deep pass (it needs the
62-step Vampire derivation of `x = (y ◇ z) ◇ x` / Eq5; the prover activates
~20 of the 60 proof clauses in 300 s).

Regression (official runner): sample_20 20/20; normal 150-slice 150/150;
hard3 399/400 (was 394/400), total 2560 s of which 642 s is hard3_0314.
Bench harness (`scripts/bench_true_prover.py`, 30 s budget, every cert
judged): hard1 24/24, hard2 100/100, hard3 194/195, normal 500/500 TRUE
problems accepted; median prover time < 0.05 s.
