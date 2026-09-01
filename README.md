# SAIR EQT2 Stage 2 solver

The Omega Institute entry to the SAIR Mathematics Distillation Challenge,
Equational Theories Stage 2 — by **Haobo Ma**, **Wenlin Zhang**, and
**Manuel Israel Cázares**.

The task: given two magma equations, decide whether one entails the other —
and prove it. Every answer must be a Lean 4 certificate the judge's kernel
actually checks: a formal proof for *true*, an explicit countermodel for
*false*. No certificate, no point.

## The solver

**[`submission/solver.py`](submission/solver.py)** — one self-contained Python
file. No dependencies, no data files.

- Frozen on **August 26**, five days before the deadline. Never changed again.
- Everything the organizers released *after* the freeze, it passed on the
  first attempt:
  - full public suite — **1889/1889**
  - Marathon track — **100/100**
  - the four announced evaluation categories — **800/800**
  - the official stress test mirroring the final leaderboard configuration —
    **200/200**
- **Zero LLM calls**, everywhere. The LLM fallback exists and never fired;
  the deterministic cascade got there first every time.

## The paper

**[`paper/main.pdf`](paper/main.pdf)** — a system description of the solver
and its evidence discipline. arXiv link will be added on announcement.

## How it works

A cheapest-first cascade. Nothing is keyed to specific problems — every answer
is derived at runtime from the two equations, and ships with its
machine-checked certificate.

- A small toolbox of known algebraic models tried first — including an exotic
  order-9 central groupoid found by our own offline search.
- Structured families: linear and affine magmas mod *n*, vector-linear and
  polynomial families — a countermodel here is a solved coefficient equation,
  not a brute-force table.
- A Latin-square-propagating finite model search for everything the families
  miss.
- For the *true* direction, an ordered unit-superposition prover whose found
  proofs are replayed as plain Lean tactic chains the kernel verifies in
  seconds.

Want to audit rather than browse? Every number above is backed by committed,
hash-bound run ledgers — start at [`PROVENANCE.json`](PROVENANCE.json). The
pre-submission review, four independent read-only audit rounds by Manuel
Israel Cázares, is preserved verbatim in this repository's pull requests.

## The Omega Institute

This solver is one artifact of a larger machine-checked mathematics program:

- [trureturing](https://github.com/the-omega-institute/trureturing) — the
  project this solver's discipline comes home to: a durable mathematical
  knowledge base where a statement is admitted only through a kernel-checked
  Lean proof, recorded in an append-only ledger, never modified in place.
- [Omega-paper-series](https://github.com/the-omega-institute/Omega-paper-series) —
  the paper series: Zeckendorf/Fibonacci combinatorics, symbolic dynamics,
  folded-rotation certificates, with reproducible scripts and Lean anchors.
- [newmath](https://github.com/the-omega-institute/newmath) — BEDC: a
  mathlib-free Lean 4 development, first-principles proofs, an autonomous
  paper-deepening pipeline.
- [automath](https://github.com/the-omega-institute/automath) — a continuously
  running Lean 4 formalization stream, source of much of the
  certificate-engineering experience behind this solver.
- [bedc-jepa-gap-ledger](https://github.com/the-omega-institute/bedc-jepa-gap-ledger) —
  does a world model know when it is guessing? A machine-checked gap ledger on
  real LLM traces.
- [equational_theories](https://github.com/the-omega-institute/equational_theories) —
  our fork of the Equational Theories Project this competition builds on.

## Why it performs the way it does

Compound interest from the projects above.

- **Lean certificate engineering.** Months of continuous formalization work
  taught us which proof shapes the kernel checks in seconds, and how far
  `decide` scales on finite structures.
- **Core-Lean discipline.** BEDC proves everything mathlib-free, from first
  principles. When the hosted judge changed Lean versions mid-competition,
  migrating every certificate family was routine — version drift had nothing
  to attach to.
- **Structured-family search.** Find the parametric family first, then verify
  inside it in closed form — the same method the paper series applies to
  combinatorial structures.
- **Measurement discipline.** Nothing is assumed that has not been measured.
  That habit, not any single algorithm, caught the three faults that would
  each have been fatal — a prover queue defect, a toolchain migration, an
  input-encoding hazard — in adversarial drills before submission, not after.

---

Private until the competition deadline (August 31, 2026, 23:59 AoE), public
immediately after. Leaderboard claims will be added once the official boards
are published.
