# Workstream contract — tagged spectral sums

WORKSTREAM: Tagged spectral sums

BASE COMMIT: assigned integration baseline

OBJECTIVE: Extend the existing lower/upper sum sandwich to arbitrary tags lying in each spectral
band and obtain the natural mesh error/convergence statements, without defining an integral.

GOVERNING DESIGN DOCUMENTS:

> **Read and obey `docs/development/SAKAI_DESIGN_CONTRACT.md` and the authoritative Sak-AI specifications it references. These requirements govern this workstream. Do not introduce designs inconsistent with them.**

OWNED MODULES: one new module under `LeanOA/Ultraweak/` and
`docs/development/reports/TAGGED_SPECTRAL_SUMS.md`.

MAY DEPEND ON: GREEN `SpectralProjection`, `SpectralSum`, and `SpectralApproximation` APIs.

MUST NOT REDESIGN: finite partitions, spectral projections, measure theory, or integration. Do not
edit existing foundational modules unless the report requests an integration-owned addition.

TARGET RESULTS: a minimal tagged-sum definition only if it has real downstream value; sandwich
between lower and upper sums; norm error bounded by mesh; a dyadic or filtered convergence theorem
when it follows without artificial assumptions.

EXPECTED PUBLIC API: theorem-level reusable facts with weakest natural assumptions; no PVM object.

VALIDATION: build the owned module; no placeholders; search Sak-AI and Mathlib first.

STOP CONDITIONS: the natural theorem requires choosing the RED integral representation.

INTEGRATION QUESTIONS: genericity and naming (IQ-002).
