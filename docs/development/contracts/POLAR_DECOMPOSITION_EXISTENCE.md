# Workstream contract — Sakai 1.12 W-star existence

WORKSTREAM: Section 1.12 polar-decomposition existence

BASE COMMIT: assigned integration baseline after WS-1 through WS-3 validation; replace this line
with the exact accepted-input commit before dispatch

OBJECTIVE: Use the regularized contractions and ultraweak compactness to construct the element
`u` in Sakai 1.12.1 and prove its factorization and initial/final support equations.

AMBIENT HYPOTHESES: use the ordinary established Sak-AI context

```text
[CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] [WStarAlgebra M].
```

Choose `WStarAlgebra.predual M` internally. Do not expose an extra predual type, `Predual`
instance, separability, first-countability, sequential-compactness, or `Nontrivial M` hypothesis in
the public theorem.

GOVERNING DESIGN DOCUMENTS:

> **Read and obey `docs/development/SAKAI_DESIGN_CONTRACT.md` and the authoritative Sak-AI specifications it references. These requirements govern this workstream. Do not introduce designs inconsistent with them.**

OWNED MODULES:

- `LeanOA/Ultraweak/ElementPolarDecomposition.lean`;
- `docs/development/reports/POLAR_DECOMPOSITION_EXISTENCE.md`.

No other worker may edit the production module while WS-4 is active.

MAY DEPEND ON: accepted Section 1.12 helpers, `Ultraweak.isCompact_closedBall`, `MapClusterPt`,
fixed-left/right multiplication continuity, and support zero-kernel APIs.

MUST NOT REDESIGN: functional polar decomposition, preduals, compactness, support, or CFC. Do not
use sequential compactness, joint ultraweak multiplication, or §1.11 integral/PVM machinery.

TARGET RESULTS: a cluster point `b` with `‖b‖ ≤ 1` and `b * CFC.abs a = a`; retain the norm bound
for Sakai's defect argument. Construct a cutdown `u` with

```text
a = u * CFC.abs a
star u * u = (rightSupport a).1
u * star u = (leftSupport a).1.
```

Then use the accepted WS-2 bridges to expose the exact source equations with the absolute values
bundled as self-adjoint elements:

```text
star u * u = (support ⟨CFC.abs a, (CFC.abs_nonneg a).isSelfAdjoint⟩).1
u * star u = (support ⟨CFC.abs (star a), (CFC.abs_nonneg (star a)).isSelfAdjoint⟩).1.
```

It is acceptable to prove the right/left-support equations first; do not weaken the final public
existence result to those internal bridge statements.

Also prove the source consequence

```text
a * star a = u * (star a * a) * star u.
```

VALIDATION: focused theorem build, explicit topology audit, `#print axioms`, no placeholders.

STOP CONDITIONS: the argument needs a subsequence merely for convenience, assumes joint
ultraweak continuity, or requires a foundational instance change.
