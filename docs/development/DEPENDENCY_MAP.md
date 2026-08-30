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
  ↓
lowerSpectralSum / upperSpectralSum
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
[RED] source-faithful ultraweak decomposition for an arbitrary competing resolution
  ↓
[RED] support recovery and uniqueness
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
`SpectralProjection` and `SpectralSum` as a narrow high-payoff chain.

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
`spectralPositivePart`. It introduces no resolution or integral object. Scratch work shows that
projection-valuedness plus monotonicity controls finite truncated-affine sums, but Sakai's actual
ultraweak representation still needs a fixed-projection decomposition argument before support and
uniqueness can move out of RED.

## Cartography fields for a major concept

For major concepts, reviews should record: Sakai source; existing Mathlib object/result; Sak-AI
declaration; direct prerequisites; downstream consumers; upstream/generalization candidate; Verso
location; and governing design constraint. Put theorem-level statement and completion data in the
relevant Verso node, not here.
