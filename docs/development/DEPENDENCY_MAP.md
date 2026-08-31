# Dependency map and library cartography

This is an architectural map, not a second theorem-status database. Verso `uses` edges remain the
source of truth for mathematical theorem dependencies.

## Major code paths

```text
lp / weak-bilinear and weak-dual infrastructure
  ↓
Predual + Ultraweak.Basic
  ↓
Ultraweak.Dual / WStarAlgebra / algebra operations
  ↓
Strong topology / normality / projection lattice
  ↓
Kaplansky density, ideals, support, central support
```

```text
Mathlib continuous functional calculus
  ↓
LeanOA CFC/order/projection staging
  ↓
CStarAlgebra.spectralPositivePart
  ↓
WStarAlgebra.spectralProjectionIio
  ├─→ projection LUB + intrinsic strong seminorm squeeze
  │     ↓
  │   exact strong left continuity (Sakai 1.11.1) [GREEN]
  │
  └─→ lowerSpectralSum / upperSpectralSum
  ↓
mesh estimates and dyadic norm convergence
  ↓
spectral-band calculus + arbitrary tagged sums
  ↓
norm convergence + named ultraweak convergence bridge
  ↓
partial-interval estimate + truncated-affine weighted-sum convergence
  ↓
CFC bridge: weighted sums converge to cfc (fun lambda => (r - lambda)^+) a
  ↓
fixed-projection ultraweak decomposition from a total difference limit [GREEN]
  ↓
[scratch] finite-cut inclusion refinement + shrinking-mesh filter + asymptotic endpoints
  ↓
[scratch] prescribed-cut moment transport + complete support recovery and uniqueness
  ↓
[scratch] same-net strong convergence implies the checked ultraweak candidate
  ↓
[RED / LEVEL C] Sakai's undefined division/refinement/improper-integral semantics
  ↓
[RED] general PVM and measurable functional calculus
```

```text
semiring annihilators + opposite transport
  ↓
ultraweakly closed one-sided ideals
  ↓
native closed TwoSidedIdeal classification
  ↓
central projections and centralSupport
```

```text
positive continuous linear maps / positive functionals
  ↓
Mathlib GNS
  ↓
strong-topology coefficient arguments
  ↓
normality and predual uniqueness
```

## Current junction nodes

Direct local-import counts identify `Ultraweak.Basic` and the weak-bilinear staging API as the
largest syntactic junctions. Semantically important junctions also include `Ultraweak.Dual`,
`Ultraweak.WStarAlgebra`, `Ultraweak.Multiplication`, `Ultraweak.ProjectionLattice`,
`PositiveContinuousLinearMap`, and the CFC order staging layer. The spectral frontier adds
`SpectralProjection`, the downstream `StrongProjection`/`SpectralProjectionStrong` bridge, and
`SpectralSum` as a narrow high-payoff chain.

Changes at these nodes receive architecture review even when the local proof is routine.

The first parallel wave exposed one reusable leaf below the projection junction:
`IsStarProjection.sub_mul_sub_eq_zero_of_le` is nonunital and independent of spectral theory. The
spectral-band and tagged-sum modules remain downstream theorem layers, so the wave did not widen the
foundational junction surface.

The D002 scratch experiment adds no public node. Its two proposed integral predicates are
kernel-equivalent for every real integrand after specializing the generic evaluator, and both lack
the arbitrary-resolution semantics used by Sakai's uniqueness proof. The next dependency edge is
therefore a concrete theorem about the continuous weight `(lambda_0 - lambda)^+`, not an integral
definition. This keeps future weighted-sum theorem work downstream of the GREEN projection API
while the family-parametric resolution object remains RED; no weighted-sum public layer is implied.

An earlier import audit with `lake shake --keep-public --explain` found broad historical removable
imports around foundational-looking modules. No imports were changed during that audit:
those modules are junction nodes, and cleanup should be performed in bounded batches with full
downstream builds rather than folded into unrelated spectral work.

The truncated-affine transaction adds one theorem-only node below the existing tagged-sum layer.
It proves a partial-interval estimate, a bandwise estimate for the CFC positive part even when the
cutoff lies inside a band, and sharp norm and specified-ultraweak convergence to the existing
`spectralPositivePart`. It introduces no resolution or integral object.

The fixed-projection transaction adds a reusable leaf at ordered $C^*$-algebra generality. From
the ultraweak limit of `u_i-v_i` and one eventual fixed-element extraction identity it derives the
individual limits; for a star projection and eventually positive pieces it identifies those
limits with positive and negative parts. Finite cutoff algebra and the subsequent support and
pointwise uniqueness chain are kernel-checked in scratch. At the end of that transaction, the
missing dependency edge was the representation/refinement bridge constructing the inserted-cut
nets from a source-facing hypothesis. No lower-family, resolution, integral, or PVM object was
added.

The refinement transaction closes that bridge conditionally. `Finset ℝ` inclusion and union reuse
Mathlib's directed order; a checked nontrivial filter adds shrinking maximum adjacent mesh while
retaining endpoint escape and eventual fixed-cut insertion. Under explicit left-endpoint moment
convergence along any such refinement-directed source, the complete finite split, support recovery,
pointwise identification, and family uniqueness chain kernel-checks. The sole remaining RED edge is
semantic: Sakai does not define his abstract Radon--Stieltjes integral by this Moore--Smith filter,
so the candidate cannot become the source theorem or public API before source-equivalence review.

The subsequent source-certification audit corrects the topology coordinate: Sakai explicitly uses
the stronger `s(M,M_*)` topology. Existing `Ultraweak.Strong` infrastructure proves in scratch that
strong convergence of the same candidate net implies the already checked ultraweak uniqueness
hypotheses. The audit nevertheless classifies the overall source semantics LEVEL C because neither
Sakai nor a uniform period convention fixes the net/filter, refinement, tags, or improper endpoint
limit. The source-equivalence edge therefore remains RED by evidence, not by missing proof
engineering.

The source-faithful 1.11.1 transaction adds no competing topology. The generic projection theorem
lives downstream of both `Strong` and `ProjectionLattice`; the spectral bridge is downstream again.
Its arbitrary-filter theorem gives exact strong left continuity and specializes to Sakai's
nonmonotone sequence statement. This production GREEN edge is independent of the scratch
Radon--Stieltjes candidate and leaves the LEVEL C boundary unchanged.

Section 1.12 has a separate dependency chain. Its first production checkpoint is
`6d24a2feb704cae6e4bedc00d6bc9f17c601f310`:

```text
Mathlib CFC.abs + projection/idempotence API
  ↓
CFC.abs_mul_eq_zero_iff / CFC.mul_abs_eq_zero_iff
IsStarProjection.mul_star_mul_self(_assoc) / mul_star_self
  ↓
WStarAlgebra.support_abs / support_abs_star
  ↓
checked regularizer in scratch + existing ultraweak compact closed ball
  ↓
element polar decomposition (Sakai 1.12.1)
```

The general $C^*$-layer and regularizer branch have been reviewed: the former is public and stable,
and the exact Sakai regularizer is kernel-checked in scratch. The latter gives contractive
regularizers
`aReg n`, `aReg n * h n = a`, `h n -> CFC.abs a`, and consequently
`aReg n * CFC.abs a -> a` in norm. Its next edge reuses `Ultraweak.isCompact_closedBall`, mapped
filter cluster points, and continuous multiplication by the fixed element `CFC.abs a`; it does not
require joint ultraweak continuity or a new compactness layer. The support bridge is now reviewed:
it identifies the two absolute-value supports with `rightSupport a` and `leftSupport a` without
unfolding or replacing the existing support construction. The WS-1--WS-3 inputs are therefore
ready for WS-4 existence work. No edge from the §1.11 integral/PVM boundary enters this chain.

## Cartography fields for a major concept

For major concepts, reviews should record: Sakai source; existing Mathlib object/result; Sak-AI
declaration; direct prerequisites; downstream consumers; upstream/generalization candidate; Verso
location; and governing design constraint. Put theorem-level statement and completion data in the
relevant Verso node, not here.
