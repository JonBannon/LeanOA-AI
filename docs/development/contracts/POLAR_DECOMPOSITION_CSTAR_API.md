# Workstream contract — C-star polar-decomposition support API

WORKSTREAM: Section 1.12 general C-star API

BASE COMMIT: `f840ec2643a255cf1fcbb5c69da316c74417829f`

OBJECTIVE: Prove the small general C-star facts needed by Sakai 1.12.1. From
`IsStarProjection (star u * u)`, derive the standard partial-isometry fixing and final-projection
identities. Prove the two exact absolute-value annihilator equivalences

```text
CFC.abs a * x = 0 ↔ a * x = 0
x * CFC.abs a = 0 ↔ x * star a = 0.
```

The second orientation is deliberately about `star a`, not `a`; arbitrary `a` need not be normal.

GOVERNING DESIGN DOCUMENTS:

> **Read and obey `docs/development/SAKAI_DESIGN_CONTRACT.md` and the authoritative Sak-AI specifications it references. These requirements govern this workstream. Do not introduce designs inconsistent with them.**

OWNED MODULES:

- a narrow new `LeanOA/Mathlib/Analysis/CStarAlgebra/Abs.lean` for the absolute-value annihilator
  facts;
- `LeanOA/Mathlib/Analysis/CStarAlgebra/Projection.lean` for projection/fixing facts;
- `docs/development/reports/POLAR_DECOMPOSITION_CSTAR_API.md` for overlap and validation notes.

If overlap or the exact dependency graph favors another narrow mirrored Mathlib-staging file,
record why in the report. Do not broaden `CStarAlgebra/Basic.lean` merely to import the CFC
absolute-value stack, and do not create a polar-decomposition-specific module for these general
facts.

MAY DEPEND ON: pinned Mathlib CFC, C-star, and projection APIs. Target
`NonUnitalCStarAlgebra` generality whenever the declarations elaborate there; add unitality only
for a theorem that genuinely uses `1`.

MUST NOT REDESIGN: `CFC.abs`, projection predicates, support, preduals, or W-star algebra. Do not
introduce `IsPartialIsometry` unless an overlap audit and immediate consumer justify it.

TARGET RESULTS: from `hu : IsStarProjection (star u * u)`, prove declarations with the mathematical
content

```text
u * (star u * u) = u
(u * star u) * u = u
IsStarProjection (u * star u).
```

Also prove exactly the two displayed `CFC.abs` equivalences above. Search for equivalent or more
general pinned/current Mathlib and Sak-AI declarations before naming or publishing them.

VALIDATION: focused build, pinned/current Mathlib and Sak-AI overlap search, no placeholders.

STOP CONDITIONS: a desired statement is false for nonnormal elements, needs a polar part already,
or would create a competing Mathlib object.
