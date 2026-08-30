# Workstream contract — spectral-band theorem cluster

WORKSTREAM: Spectral-band theorem cluster

BASE COMMIT: assigned integration baseline

OBJECTIVE: Add a bounded, reusable theorem API for differences of existing lower spectral
projections, sufficient for finite additivity and tagged sums without introducing a set-indexed
spectral measure.

GOVERNING DESIGN DOCUMENTS:

> **Read and obey `docs/development/SAKAI_DESIGN_CONTRACT.md` and the authoritative Sak-AI specifications it references. These requirements govern this workstream. Do not introduce designs inconsistent with them.**

OWNED MODULES: one new module under `LeanOA/Ultraweak/` and
`docs/development/reports/SPECTRAL_BANDS.md`.

MAY DEPEND ON: GREEN projection and spectral-projection APIs.

MUST NOT REDESIGN: `spectralProjectionIio`, projection lattice instances, predual interfaces, or a
future set-indexed PVM. Do not edit existing foundational modules unless the report requests a tiny
integration-owned API addition.

TARGET RESULTS: projection status of ordered differences, canonical commutation, telescoping/finite
additivity, and orthogonality for disjoint ordered bands when supported cleanly by existing APIs.

EXPECTED PUBLIC API: small named theorems; introduce no bundled spectral-family structure.

VALIDATION: build the owned module; no placeholders; search Mathlib and Sak-AI first.

STOP CONDITIONS: a proof requires a competing projection representation or foundational instance.

INTEGRATION QUESTIONS: generic versus spectral-specific placement (IQ-002).
