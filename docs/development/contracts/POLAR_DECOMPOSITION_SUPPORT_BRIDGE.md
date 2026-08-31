# Workstream contract — absolute-value support bridge

WORKSTREAM: Section 1.12 W-star support bridge

BASE COMMIT: assigned integration baseline after the WS-1 annihilation interface is frozen;
replace this line with the exact commit before dispatch

OBJECTIVE: Identify the support of Mathlib's absolute value with Sak-AI's existing one-sided
supports, in the exact orientations required by Sakai 1.12.1.

GOVERNING DESIGN DOCUMENTS:

> **Read and obey `docs/development/SAKAI_DESIGN_CONTRACT.md` and the authoritative Sak-AI specifications it references. These requirements govern this workstream. Do not introduce designs inconsistent with them.**

OWNED MODULES:

- a narrow new `LeanOA/Ultraweak/AbsSupport.lean`, downstream from both `Support` and the accepted
  C-star absolute-value module;
- `docs/development/reports/POLAR_DECOMPOSITION_SUPPORT_BRIDGE.md`.

MAY DEPEND ON: GREEN `Ultraweak.Support`, Mathlib `CFC.abs`, and the accepted C-star annihilation
lemmas.

MUST NOT REDESIGN: support projections, one-sided support orientation, CFC, or the projection
lattice. Do not assume `abs (star a) = abs a` for arbitrary `a`, and do not force CFC imports into
the foundational `Ultraweak.Support` module merely to host this bridge.

TARGET RESULTS: source-facing bridges, with the positive absolute values bundled as
`selfAdjoint M`, whose mathematical content is

```text
support (|a|) = rightSupport a
support (|star a|) = leftSupport a.
```

Derive them from the accepted WS-1 annihilator equivalences and the existing support kernel API.
Before adding any further zero-kernel corollary, perform an overlap search and identify a concrete
consumer in WS-4; otherwise keep the bridge surface minimal.

VALIDATION: focused build, orientation tests on nonnormal examples where feasible, no placeholders.

STOP CONDITIONS: the proof would require a new support object or an unproved normality assumption.
