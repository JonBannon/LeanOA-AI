# Workstream contract — Mathlib spectral/integration reconnaissance

WORKSTREAM: Mathlib spectral/integration reconnaissance

BASE COMMIT: assigned integration baseline

OBJECTIVE: Determine the shortest Mathlib-compatible route from Sak-AI's finite spectral sums to a
faithful formulation of Sakai 1.11.3, and identify duplication relevant to the active frontier.

GOVERNING DESIGN DOCUMENTS:

> **Read and obey `docs/development/SAKAI_DESIGN_CONTRACT.md` and the authoritative Sak-AI specifications it references. These requirements govern this workstream. Do not introduce designs inconsistent with them.**

OWNED MODULES: `docs/development/reports/MATHLIB_SPECTRAL_AUDIT.md` only.

MAY DEPEND ON: all repository sources and pinned Mathlib, read-only; current Mathlib sources/history
when available.

MUST NOT REDESIGN: spectral projections, preduals, measure theory, or integration interfaces.

TARGET RESULTS: exact existing declarations and files; viable interface alternatives; missing
infrastructure; overlap/upstream findings; recommendation with explicit reversibility risks.

EXPECTED PUBLIC API: none.

VALIDATION: cited local paths/declaration names must exist; distinguish pinned from current Mathlib.

STOP CONDITIONS: evidence requires a foundational choice; record options without choosing it.

INTEGRATION QUESTIONS: IQ-001 and IQ-002.
