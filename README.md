# SAIR EQT2 Stage 2 solver

The Omega Institute entry to the SAIR Mathematics Distillation Challenge,
Equational Theories Stage 2 — by Haobo Ma, Wenlin Zhang, and Manuel Israel
Cázares.

The task: given two magma equations, decide whether one entails the other, and
prove it — every answer must be a Lean 4 certificate the judge's kernel
actually checks, a formal proof for "true" or an explicit countermodel for
"false". No certificate, no point.

**The solver**: [`submission/solver.py`](submission/solver.py) — one
self-contained Python file, no dependencies, no data files. It was frozen on
August 26, five days before the deadline, and never changed again. Everything
the organizers released after the freeze it passed on the first attempt: the
full public suite (1889/1889), the Marathon track (100/100), the four announced
evaluation categories (800/800), and the official stress test mirroring the
final leaderboard configuration (200/200) — all with **zero LLM calls**. The
LLM fallback exists and never fired; the deterministic cascade got there first
every time.

**The paper**: [`paper/main.tex`](paper/main.tex) — a system description of the
solver and its evidence discipline (arXiv link will be added on announcement).

## How it works, in one paragraph

The solver runs a cheapest-first cascade. It first tries a small toolbox of
known algebraic models (including an exotic order-9 central groupoid found by
our own offline search), then searches structured families — linear and affine
magmas mod n, vector-linear and polynomial families — where a countermodel is a
solved coefficient equation rather than a brute-force table; then a
Latin-square-propagating finite model search; and for the "true" direction, an
ordered unit-superposition prover whose found proofs are replayed as plain Lean
tactic chains the kernel verifies in seconds. Nothing is keyed to specific
problems: every answer is derived at runtime from the two equations, and every
answer ships with its machine-checked certificate. For readers who want to
audit rather than browse, every number above is backed by committed,
hash-bound run ledgers ([`PROVENANCE.json`](PROVENANCE.json)), and the
pre-submission review — four independent read-only audit rounds by Manuel
Israel Cázares — is preserved verbatim in this repository's pull requests.

## The Omega Institute

This solver is one artifact of the Omega Institute's machine-checked
mathematics program. Related public repositories:

- [Omega-paper-series](https://github.com/the-omega-institute/Omega-paper-series) — the paper series:
  Zeckendorf/Fibonacci combinatorics, symbolic dynamics, folded-rotation certificates, and more, each
  with reproducible scripts and Lean anchors where applicable.
- [newmath](https://github.com/the-omega-institute/newmath) — BEDC (Binary Emission Discovery
  Calculus): a mathlib-free Lean 4 development with first-principles proofs and an autonomous
  paper-deepening pipeline.
- [automath](https://github.com/the-omega-institute/automath) — a continuously running Lean 4
  formalization stream (mathlib-based), source of much of the certificate-engineering experience
  behind this solver.
- [bedc-jepa-gap-ledger](https://github.com/the-omega-institute/bedc-jepa-gap-ledger) — does a world
  model know when it is guessing? A machine-checked gap ledger on real LLM traces.
- [equational_theories](https://github.com/the-omega-institute/equational_theories) — our fork of the
  Equational Theories Project this competition builds on.
- [trureturing](https://github.com/the-omega-institute/trureturing) — the project this solver's
  discipline comes home to: a durable mathematical knowledge base in which a statement is admitted
  only through a kernel-checked Lean proof, recorded in an append-only attestation ledger, and never
  modified in place. The certificate-first rules this solver applies competitively are the same rules
  trureturing applies to lasting mathematical truth.

## Why this solver performs the way it does

The solver's results are the compound interest of the projects above.

- **Lean certificate engineering.** Months of continuous Lean 4 formalization work (the `automath`
  stream and the paper series' Lean anchors) built the working knowledge this solver's certificate
  emitters are made of: which proof shapes the kernel checks in seconds, how far `decide` scales on
  finite structures, and how namespaces interact with a judge's declaration policy.
- **Core-Lean proof discipline.** The BEDC development in `newmath` is deliberately mathlib-free:
  every proof from first principles in core Lean. When the competition's hosted judge moved to a new
  Lean version mid-competition, migrating every certificate family to core-only was routine here —
  version drift in an external library simply has nothing to attach to.
- **Structured-family search.** The countermodel stages search parameterized algebraic families
  (linear, affine, vector-linear, polynomial) with closed-form coefficient checks rather than raw
  enumeration — the same method the paper series applies to combinatorial structures: find the
  parametric family first, then verify inside it in closed form.
- **Measurement discipline.** Every claim carries a machine-checked certificate or a hash-bound
  ledger, and nothing is assumed that has not been measured. That discipline, rather than any single
  algorithm, is what caught the three faults that would each have been fatal in a one-submission
  competition: a prover selection-queue defect, a toolchain migration, and an input-encoding hazard —
  all found by adversarial drills before submission, not after.

This repository was kept private until the competition deadline
(August 31, 2026, 23:59 AoE) and made public immediately after. Leaderboard
claims will be added only once the official boards are published.
