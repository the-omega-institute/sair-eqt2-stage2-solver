# Draft status

Target format: CPP 2027, ACM `acmart` `sigplan`. CPP uses lightweight
double-blind review, so the paper builds two ways: `\ANONSUBMISSION` gives the
anonymized HotCRP submission ([anonymous,review], no author block, no CRediT);
the default build is the arXiv/camera-ready version with authors and the CRediT
statement. This is a working draft, not a submission claim.

## Placeholders

- Author order RESOLVED 2026-08-24: Haobo Ma (ChronoAI Pte. Ltd.), Wenlin Zhang
  (NUS), Israel Cazares (Bytepro AI, Mexico). CRediT lines for Haobo and Wenlin
  are in; Israel writes his own lines (TODO marker in main.tex).
- The exact bibliographic title for arXiv:2604.18897 is TBD; the citation is
  currently keyed by author and arXiv identifier only.
- The hosted-results material reports only the playground measurement. A
  post-leaderboard v2 must add the submission timestamp, uploaded solver hash,
  official score/rank, and public result URL, then remove the `PENDING` status.
- Conference date/location and ACM rights metadata are intentionally unset.

## Evidence boundary

- No hosted leaderboard score, hidden-set transfer claim, completeness theorem,
  general LLM-ineffectiveness claim, or comparative-superiority claim appears.
- The requested random 150-pair order-5 row was omitted because none of the
  authoritative sources contains that measurement. The sourced order-5 drill
  row is `evaluation_order5`, 200/200.
- `PROVENANCE.json` records the completed hosted playground measurement as
  200/200, while `CLAIMS_LEDGER.md` still mentions only the first 100/100. The
  draft follows the newer provenance record and the explicit drafting brief;
  synchronize the claims-ledger sentence before submission.
- `results/PUBLIC_SETS_BASELINE_20260819.md` is absent from this worktree but was
  read from repository commit `e00a349`; the current-paper tables use the v2.4
  bindings in `PROVENANCE.json`, not that superseded v1 report.

## Build status

- Portable fallback: `make plain` passes with `pdflatex` and BibTeX.
- Output: 12 pages total in fallback mode. The manuscript fills 10 pages and
  continues onto page 11; references occupy the rest of page 11 and page 12.
  There are no overfull boxes, undefined citations, or undefined references.
- ACM mode could not be compiled locally because `acmart.cls` is not installed;
  `main.tex` still targets `\documentclass[sigplan,screen]{acmart}` by default.
- All 12 fallback pages were rendered with Poppler and visually inspected.
