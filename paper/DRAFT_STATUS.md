# Draft status

Target format: CPP 2027, ACM `acmart` `sigplan`. CPP uses lightweight
double-blind review, so the paper builds two ways: `\ANONSUBMISSION` gives the
anonymized HotCRP submission ([anonymous,review], no author block, no CRediT);
the default build is the arXiv/camera-ready version with authors and the CRediT
statement. This is a working draft, not a submission claim.

## Placeholders

- Author order RESOLVED 2026-08-24: Haobo Ma (ChronoAI Pte. Ltd.), Wenlin Zhang
  (NUS), Israel Cazares (Bytepro AI, Mexico). CRediT lines for Haobo and Wenlin
  are in; all three CRediT lines are in (Israel supplied his by email, 2026-08-25). Name form: Manuel Israel Cázares.
- The exact bibliographic title for arXiv:2604.18897 is TBD; the citation is
  currently keyed by author and arXiv identifier only.
- Conference date/location and ACM rights metadata are intentionally unset.

## Evidence boundary

- No hosted leaderboard score, hidden-set transfer claim, completeness theorem,
  general LLM-ineffectiveness claim, or comparative-superiority claim appears.
- The requested random 150-pair order-5 row was omitted because none of the
  authoritative sources contains that measurement. The sourced order-5 drill
  row is `evaluation_order5`, 200/200.
- Hosted-playground and pre-upgrade Lean 4.32 results are reported as external
  operator attestations, matching `PROVENANCE.json`; the paper tables are
  regenerated programmatically from the v2.5 bindings in `PROVENANCE.json`.

## Build status

- All three build modes compile with zero errors; per-mode pdflatex/bibtex logs
  are committed under `paper/build_logs/` as the verification artifact:
  plain-article fallback (`make plain`, pdflatex + BibTeX, 13 pages), ACM
  `sigplan,screen` default (12 pages; `acmart.cls` is installed in the local
  texmf tree), and the anonymized `\ANONSUBMISSION` CPP submission mode.
- There are no undefined citations or undefined references in any mode.

## Review status

- Manuel Israel Cázares reviewed the full draft (2026-08-25): every checked
  number ledger-backed, architecture matches the code, dual-build works; no
  substantive concerns. His optional note on the FATE-X execution-check cost
  figure is incorporated (billed-delta figures only; per-call latency is
  recorded as unavailable in the run notes and stays out).

## Freeze binding (v2.5)

The paper's solver identity, tables, and provenance rows are bound to the frozen v2.5 artifact
(SHA-256 `f2392533c9f4c03b292be80bc6d12e98e5254cc4861d1cc4b227957ad5ed89b4`, 189,504 bytes). Hosted-playground results (all four
categories at 100%) and the pre-upgrade Lean 4.32 corpus check are reported as external operator
attestations; the repository-verifiable toolchain evidence for the exact v2.5 artifact is the
committed Lean 4.33.1 revalidation (`results/lean4331_revalidation/`, hash-bound in PROVENANCE).
A post-leaderboard v2 must still add the hosted submission timestamp, official score, and result URL.
