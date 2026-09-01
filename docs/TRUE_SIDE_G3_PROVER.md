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

## Prover speed / strategy pass (branch wenlin/v2-prover-speed)

Scope: `_G3*` block and `g3_prove` only (same certificate emitter, same
stage structure in `main()`).

### Root cause of the `hard3_0314` failure (2923 => 1623)

It was not throughput.  `_G3Prover.demodulate` stopped rewriting when a
demodulation step made both sides equal (`make_step` returns `None` for
`after == other`) and kept the *partially* rewritten equation.  Every
instance of the hypothesis (and every other tautology reachable by
demodulation) therefore survived as a small active clause: the trace for
2923 shows selections 56-81 being `f(x0, h_lhs) = f(x0, x2)`,
`f(f(f(x0,f(x1,f(x2,x3))),x0),x1) = x1`, ... (all instances of `h`).  The
given-clause loop spent its budget on these and never reached the ~60
proof clauses of the Vampire derivation.  `backward_simplify` had the same
hole (an active clause rewritten to a tautology stayed active).

Fix: a demodulation step that yields `s = s` deletes the clause
(`demodulate` returns `None`; `backward_simplify` retires the clause before
checking the result).  With only this change 2923 => 1623 is proved in
0.6 s (58 given clauses, cap 60, default selection).

### Throughput changes (behaviour-preserving, same search trace)

- `_g3_unify` returns the triangular substitution (no eager full
  application); `_g3_subst` already resolves chains.
- `make_step` (superposition): instantiated sizes are computed from static
  sizes + per-equation variable counts (`_G3Eq.varcounts`, cached position
  lists `_G3Eq.tpos` with per-position counts) and the size-cap rejection
  happens *before* any term is built; survivors are built with a memoised,
  structure-sharing substitution (`_g3_subst_m`).  Previously every
  successful unifier (~220 k per 10 k survivors on `etp_450_432`) built the
  full instantiated terms and re-traversed them for sizes.
- Unifiers are memoised by value per prover (`ucache`: `(renamed lhs,
  renamed subterm) -> (unifier, size memo)`; hit rate 60-75 %).
- `superpose` skips positions whose uninstantiated lower bound already
  exceeds the size cap.
- KBO: cached term sizes / variable counts (`_g3_sz`, `_g3_vc`),
  `normalize` passes the known size; iterative `_g3_match`, `_g3_preorder`.

### Strategy changes

- Round schedule `[(24, 6%), (32, 12%), (44, 25%), (60, 55%),
  (80, 80%, vp=1/ar=4), (120, 100%, vp=0/ar=2/var_cap+2)]`; a round that
  saturates (capped passive queue empty) hands its time to the next one,
  and if the last round saturates with time left the caps keep growing
  (+40 size, +2 variables) up to 400.  Previously a saturated cap-60 round
  ended the search with the budget unspent (`etp_3051_3082`, `etp_463_491`
  need a weight-62 intermediate and were unreachable).

### Measurements

Prover only (`g3_prove`, this machine, 6-8 worker processes):

| set | before | after |
|---|---|---|
| 11 TRUE residuals (`scripts/data/v2_true_residuals.json`, 6 s) | 10/11, hard3_0314 unsolved at 600 s | 11/11, hard3_0314 in 0.7-0.9 s (cap-44 round) |
| ETP Vampire-hard 254 (`scripts/data/etp_vampire_hard.json`, 30 s) | 242/254, sum 320 s | 254/254, max 2.7 s, sum 16 s |
| remaining 1253 ETP Vampire pairs (10 s) | - | 1252/1253 (the miss is `x = y`, handled by stage 2b) |
| public TRUE problems (819, 6 s) | 818/819 | 819/819, median 1 ms, max 1.2 s |

Fixed-search throughput (same trace, `etp_450_432` 2923-like saturation,
cap 40 / cap 60, default selection): 9.2 s / 17.0 s (tautology fix only)
-> 1.7 s / 4.2 s (all changes), i.e. 4-5x.  cProfile before: `_g3_subst`
+ `_g3_size` 14.3 s of 40 s; after: unify/occurs + index lookup dominate.

Official judge (`pipeline.runner`, rev of `eqt2-stage2` checkout):
residuals 11/11 (hard3_0314 solved in 14.6 s wall, was 810 s fail),
sample_20 20/20, normal 150-slice 150/150 (see report for medians).

### Still open

- Memory guards: `max_neg` (25 k stored goal clauses), unifier/term
  caches bounded (100 k / 150 k entries, cleared per prover), clause and
  normal-form budgets scaled by 60/size_cap for the relaxed-cap rounds.
  600 s deep pass on a FALSE input (hard1_0062, pure saturation): 995 MB
  max RSS (frozen solver: 941 MB; sandbox limit 2048 MB).
- For FALSE inputs with large goals the negative-clause paramodulation
  (`superpose_into_neg`) still dominates time; irrelevant to provability
  but it is the next throughput item.
- Demodulation-heavy theories (many unoriented rules): `normalize` ->
  index lookup + `_g3_match` + KBO checks dominate; a flatterm/hash-consed
  term representation would be the next 2-3x.
