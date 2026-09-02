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
positive-functional Cauchy--Schwarz and zero-coefficient helpers
  ↓
PositiveLinearMap.nullIdeal [general unital C*-algebra]
  ↓
explicit IsNormalOnProjections proof
  ↓
strong-seminorm zero set is closed
  ↓ existing convex strong-to-ultraweak closure bridge
ultraweakly closed null ideal
  ↓ existing closed-left-ideal classifier
PositiveLinearMap.support [intrinsic W*-algebra API; chosen predual hidden]
  ↓
annihilation, greatest-zero, cutdown, and theorem-level faithfulness interfaces
  ↓
support_le_iff_apply_eq_apply_one + support-zero implies norm orthogonality [GREEN]
  ├─→ PositiveLinearMap.IsOrthogonal [general nonunital API] [GREEN]
  │     + existing self-adjoint-unitary positive factorization [GREEN]
  │     + ultraweak corner cutdowns and explicit projection normality [GREEN]
  │     ↓
  │   private complementary-carrier construction and exact norm identity
  │     ↓
  │   Ultraweak.existsUnique_orthogonal_decomposition_of_isSelfAdjoint [GREEN]
  │     ↓
  │   support_mul_eq_zero_of_isOrthogonal + isOrthogonal_iff_support_mul_eq_zero [GREEN]
  │
  └─→ full-unit-ball exposed-face factorization with source right action [private engine]
        + PositiveLinearMap.conjugate and preservation of normality [GREEN]
        + functional support carrier and uniqueness API [GREEN]
        ↓
      Ultraweak.existsUnique_functional_polar_decomposition_basic [GREEN]
        ↓
      Ultraweak.functionalAbs + final support transport under adjoint [GREEN]
        ↓
      Ultraweak.existsUnique_functional_polar_decomposition [Sakai 1.14.4] [GREEN]
        ↓
      Section 1.15 topology/API audit and Proposition 1.15.1 [frontier]
```

```text
Mathlib ContinuousLinearMapWOT [concrete WOT]
  + Mathlib PointwiseConvergenceCLM [pointwise/SOT]
  ↓
PointwiseConvergenceCLM.toWOT
  + WOT-closed implies pointwise/SOT-closed [general mirrored-Mathlib bridges; GREEN]

ContinuousLinearMap.vectorFunctional
  + vectorFunctionalSpan [separating, intrinsic-star and multiplier invariant; GREEN]
  ↓
ContinuousLinearMapWOT.vectorFunctionalWeakEquiv [bidirectional raw/span WOT bridge; GREEN]
  ↓
ContinuousLinearMapWOT.vectorFunctionalPairing_isWeak
  + vectorFunctionalSpanEquivDual [σ(B(E,F),V) = WOT and full WOT dual; GREEN]

specified-predual Ultraweak σ(M,P)
  + intrinsic Strong s(M,P)
  + SakaiMackey / SakaiInvariantTestSpace / Kaplansky density
  ↓
Strong.image_closure_toUltraweakEquiv
  ↓
Strong.isClosed_iff_image_toUltraweakEquiv [real-convex intrinsic bridge; GREEN]

[GREEN] finite vector-coefficient realization of WOT
  ↓
[GREEN] norm closure and concrete predual of B(H)
  ↓
[GREEN] countable coefficient-series test space
  + [GREEN] full-predual topology → series-test topology
  ↓
[DEFERRED to Cor. 1.15.5--1.15.6] converse series representation / topology equality
  + [RED] concrete ultrastrong ↔ intrinsic s comparison
  + [GREEN] relative Kaplansky density in Mathlib's WOT closure
  ↓
Sakai Proposition 1.15.1 [NOT SOURCE-FORMALIZED; relative-density Verso node complete]
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
private production regularizer + existing ultraweak compact closed ball
  ↓
ultraweak cluster equation b * |a| = a
  ↓
support-defect cutdown u = q * b * p
  ↓
factorization + exact initial/final supports [GREEN, WS-4]
  ↓
algebraic uniqueness from factorization + initial supports [GREEN, WS-5]
  ↓
exact `ExistsUnique` Sakai 1.12.1 package + Verso node [GREEN, WS-5]
```

The general $C^*$-layer and support bridge are public and stable. WS-4 privately transplants the
exact Sakai regularizer, obtains a contractive cluster point with
`Ultraweak.isCompact_closedBall`, and passes `aReg n * CFC.abs a -> a` from norm to ultraweak
convergence using only fixed-right-multiplication continuity. Sakai's cutdown
`u = q * b * p` then gives the factorization and both support equations in
`WStarAlgebra.exists_element_polar_decomposition`. No sequence extraction, joint ultraweak
continuity, exposed predual parameter, or edge from the §1.11 integral/PVM boundary is used. The
algebraic theorem `WStarAlgebra.element_polar_decomposition_unique` then uses only the
factorization, the two initial-support equations, and the established support zero-kernel API.
`WStarAlgebra.existsUnique_element_polar_decomposition` packages all three source conditions.
Section 1.12 is GREEN and source-formalized.

The Section 1.13 production waves close the source-normality, orthogonal-sum, and complete-
additivity branches:

```text
projection complete lattice + directed LUB convergence [GREEN]
  ↓
projection normality ⇔ ultraweak continuous dual [GREEN]
  ↓
full Scott continuity ⇔ bounded directed-positive normality [GREEN]
  ↓
exact Sakai 1.13.2 [GREEN]

orthogonal projection family
  ↓
finite partial sums + projection/ambient LUB [GREEN]
  ↓
ultraweak/strong convergence to projection supremum [GREEN]
  ↓
normality ⇒ arbitrary-index HasSum [GREEN]
  ↓
maximal orthogonal decomposition of projection chains [GREEN]
  ↓
complete additivity ⇒ chain-LUB preservation ⇒ normality [GREEN]
  ↓
normality ⇔ complete additivity [GREEN]

continuous-dual identification + canonical predual equivalence [GREEN]
  ↓
Sakai 1.13.3 predual uniqueness [GREEN]
```

The second production wave supplies the pure projection-order/connective edge. A Zorn-maximal
orthogonal family has finite sums dominated by chain members and supremum equal to the chain LUB.
Chain-restricted Scott continuity is then sufficient for the existing cutoff/selection
characterization of normality. No spectral integral, PVM, or element polar decomposition lies on
this dependency path. The reconnaissance and completed proofs are recorded in
`reports/SAKAI_1_13_COMPLETE_ADDITIVITY_RECON.md`,
`reports/PROJECTION_CHAIN_ORTHOGONAL_DECOMPOSITION.md`, and
`reports/SAKAI_1_13_COMPLETE_ADDITIVITY.md`.

Section 1.14.2 follows a single support construction. The reusable $C^*$-level inputs are the two
Cauchy--Schwarz coefficient-vanishing orientations
`apply_star_mul_eq_zero_of_apply_star_mul_self_eq_zero_left` and
`apply_star_mul_eq_zero_of_apply_star_mul_self_eq_zero_right`; the general algebraic bridge is
`Ideal.mem_span_singleton_one_sub_iff_mul_eq_zero` for an idempotent in a ring. Normality enters
only at topological closedness. The implementation mirrors Sakai by deriving ultraweak closedness
from strong closedness, then reuses the established one-sided ideal classifier. Functional support
is not identified with element support, and support-corner faithfulness reuses the existing
`IsStarProjection.Corner` rather than adding a predicate or structure.

Definition 1.14.1 adds the independent source relation `PositiveLinearMap.IsOrthogonal` at
nonunital $C^*$-algebra generality. Theorem 1.14.3 then combines the existing
`Ultraweak.exists_positive_comp_mulLeft_of_isSelfAdjoint` factorization, complementary ultraweak
corner cutdowns, and the functional-support carrier API. The exact public endpoint is
`Ultraweak.existsUnique_orthogonal_decomposition_of_isSelfAdjoint`. Support-product zero is proved
equivalent only afterward, through `PositiveLinearMap.support_mul_eq_zero_of_isOrthogonal` and
`PositiveLinearMap.isOrthogonal_iff_support_mul_eq_zero`, so the dependency is noncircular. See
`reports/SAKAI_1_14_1_1_14_3_JORDAN_DECOMPOSITION.md`.

Theorem 1.14.4 does not reinterpret that self-adjoint theorem. The older
`Ultraweak.PolarDecomposition` supplies only a self-adjoint functional factored through left
multiplication by a self-adjoint unitary. The distinct downstream module
`Ultraweak.FunctionalPolarDecomposition` runs the exposed-face argument over the full unit ball and
produces the source convention `g x = φ (x * v)` directly. Its public dependency chain is:

```text
PositiveLinearMap.conjugate [nonunital C*-algebra]
  + PositiveLinearMap.IsNormalOnProjections.conjugate
  + PositiveLinearMap.support_conjugate_eq_mul_star
  ↓
existsUnique_functional_polar_decomposition_basic
  ↓
functionalAbs / functionalAbs_isNormalOnProjections / functionalAbs_spec
  + norm_functionalAbs / eq_functionalAbs_of_polar_decomposition
  ↓
functional_polar_decomposition_final_projection
  ↓
existsUnique_functional_polar_decomposition [exact Sakai 1.14.4]
```

The basic theorem packages right factorization, norm equality, initial support, and uniqueness.
The canonical `functionalAbs` is introduced only after that uniqueness theorem, because the source
names the positive factor and its adjoint support occurs in the final-projection clause. Initial
support remains the partial-isometry certificate; no parallel predicate, bundled normal
functional, chosen polar element, or second support object is introduced. Section 1.14 is GREEN.
The next dependency reconnaissance was the Section 1.15 topology/API audit, with Proposition
1.15.1 as the first bounded source target.

The first Section 1.15 transaction completes that direct source and overlap audit. The second
constructs the finite coefficient span, proves that its induced weak topology is exactly Mathlib
WOT in both directions, and identifies it with all WOT-continuous linear functionals. The third
computes the exact coefficient norm, constructs its norm closure, and certifies canonical
evaluation as an isometric dual equivalence and specified predual. The fourth proves norm
summability and evaluation for separately square-summable coefficients, packages the invariant
finite core, forms Sakai's countable series-test span, and proves the full-predual-to-series-test
continuous identity. It closes only the source-safe direction of the coefficient-series edge; the
later converse representation and ultrastrong comparison remain. The fifth transaction proves
ambient-relative unit-ball density in an explicit test-weak closure, identifies the finite-core
test-weak closure with Mathlib WOT, and instantiates the result for bounded operators. Pinned
Mathlib commit
`476ab284693e554a6b48c5f5210cb4fb5ae51252` supplies the concrete WOT and pointwise/SOT synonyms;
the mirrored local modules contribute the continuous SOT-to-WOT identity, the coefficient API,
and the exact weak-pairing/WOT identification. Original LeanOA commit
`cb811c1006ae78a0ff1d175253200e1859843370` contributes no concrete operator-topology bridge.
Current Mathlib still supplies neither this concrete $B(H)$
predual/double-commutant bridge nor the missing source comparisons; the predual bridge is local
Sak-AI infrastructure. The intrinsic `σ`, `s`, and
Mackey APIs therefore remain distinct from concrete WOT, SOT, $\sigma$-WOT, and ultrastrong
topologies until named compatibility theorems are proved.

## Cartography fields for a major concept

For major concepts, reviews should record: Sakai source; existing Mathlib object/result; Sak-AI
declaration; direct prerequisites; downstream consumers; upstream/generalization candidate; Verso
location; and governing design constraint. Put theorem-level statement and completion data in the
relevant Verso node, not here.
