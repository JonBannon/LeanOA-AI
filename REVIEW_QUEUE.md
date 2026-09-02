# Sak-AI human review queue and upstream opportunities

Last updated: 2026-09-01

## DESIGN REVIEW REQUEST: semiring two-sided ideals and annihilators

### Question

Should Sak-AI merely keep two-sided annihilators at Mathlib's current ring boundary, or should it
prepare an upstream proposal to generalize `TwoSidedIdeal` so the natural semiring construction is
available?

### Mathematical need

Left and right annihilators of subsets need only semiring structure. The annihilator of a
one-sided ideal is also naturally closed under addition and multiplication on both sides without
using additive inverses. Sakai later needs this only for C-star algebras, but the connective API is
genuinely algebraic.

### Existing Sak-AI situation

The Section 1.10 design puts one-sided annihilators over semirings using infima of `LinearMap.ker`.
It plans to package annihilators of one-sided ideals as native `TwoSidedIdeal`; that second step is
currently restricted to nonunital rings solely by the upstream structure.

### Upstream evidence

Pinned Mathlib defines `TwoSidedIdeal R` as a wrapper around `RingCon R`, requiring
`NonUnitalNonAssocRing R`. Its set-based constructor `TwoSidedIdeal.mk'` also has that ring
boundary. Current Jireh Loreaux LeanOA has no competing support-projection or annihilator API.

### Review precedent

Mathlib PR [#40776](https://github.com/leanprover-community/mathlib4/pull/40776) renamed the wrapper
constructor to `ofRingCon`. Its rationale explicitly notes that a future refactor could make `mk'`
the real constructor “to generalize to semirings.” No current Mathlib PR was found that performs
that refactor. Open PRs
[#42093](https://github.com/leanprover-community/mathlib4/pull/42093),
[#42095](https://github.com/leanprover-community/mathlib4/pull/42095), and
[#42100](https://github.com/leanprover-community/mathlib4/pull/42100) develop topological closure,
closed-ideal CFC, and spectral projections, but are not merged precedent.

### Candidate A

Keep Sak-AI's one-sided annihilators at semiring generality and expose native two-sided
annihilators only for rings.

Benefits: uses stable Mathlib objects, requires no new structure, is enough for Section 1.10, and
is easy to upstream piecemeal. Drawback: the two-sided packaging has a stronger assumption than
the mathematics.

### Candidate B

Design a Mathlib refactor in which `TwoSidedIdeal` has a set-based semiring representation and
ring congruences become a conversion/equivalence available under additive inverses.

Benefits: reaches the natural algebraic boundary and fulfills the direction anticipated in
#40776. Drawbacks: foundational, wide in refactoring radius, and inappropriate to prototype by
editing the read-only dependency.

### Agent recommendation

Use Candidate A for Sakai Section 1.10. Treat Candidate B as a separate upstream design project
only if a human reviewer wants to pursue it. Do not add a local competing two-sided-ideal type.

### Refactoring radius

Candidate A affects only the new annihilator module. Candidate B would affect Mathlib's
`TwoSidedIdeal` constructors, lattice, quotient/congruence interface, and downstream files.

### Upstream implication

Candidate A may yield small upstreamable annihilator lemmas. Candidate B necessarily requires a
Mathlib change and must not be implemented in the dependency checkout.

### Reversibility

Candidate A is readily generalized later because its statements already use the native object.
Candidate B is difficult to reverse after downstream adoption.

### What work can safely continue meanwhile

Verso migration, the semiring one-sided annihilator layer, the general projection-orthogonality
lemma, and promotion of the internal-unit projection lemma do not depend on this decision.

Human review is requested on whether the upstream semiring refactor should become an active
proposal or remain a recorded opportunity.

## Other upstream opportunities to monitor

- `IsStarProjection.mul_eq_self_of_nonneg_of_le_of_mul_eq_self` is a general C-star-algebra
  hereditary-support lemma introduced in Sak-AI's Mathlib extension layer. It has no W-star or
  topology assumptions and is a plausible small upstream contribution after API review.
- Mathlib PR #42093 may eventually replace local generic topological-closure staging for
  `TwoSidedIdeal`.
- Mathlib PR #42095 may supply closed-ideal continuous-functional-calculus closure used after
  Section 1.10.
- Mathlib PR #42100 remains relevant to future compatibility of spectral-projection naming, but
  its clopen-set construction does not replace Sakai's W-star half-line support projections.

These are current open work, not dependencies or accepted API precedent.

## Current overlap audit for the completed Section 1.10 layer

The 2026-08-27 comparison used Mathlib master commit
`39c86ed8eb69c9ef854f1f2de1b7b7bd171fef15` and current LeanOA commit `dd09e90` as read-only
references. Searches of the relevant source directories found no existing central-support,
closed-two-sided-ideal/central-projection classification, or equivalent annihilator API. Searches
of Mathlib pull-request titles and bodies likewise found no overlapping central-support proposal.

PRs #42093, #42095, and #42100 remain open. They concern topological closure of two-sided ideals,
closed-ideal CFC, and clopen spectral projections respectively; they do not replace the completed
Section 1.10 API. The #42100 review used for the Section 1.11.1 target is recorded below.

## Overlap audit for the Sakai 1.11.1 checkpoint

The 2026-08-28 comparison used pinned Mathlib commit
`476ab284693e554a6b48c5f5210cb4fb5ae51252`, Mathlib master commit
`9f2515783c2252157110d15dbfbbf8dd5795dba8`, and the read-only LeanOA checkout at
`cb811c1006ae78a0ff1d175253200e1859843370`. No existing W-star lower-spectral-projection or
continuity-from-below declaration was found.

Mathlib PR #42100 was open at head `7f7138a127bf5c2f91d5b3e30b58499139561672`. It constructs
continuous-functional-calculus projections from indicators of clopen subsets of the quasispectrum.
The half-line `Set.Iio r` need not be clopen on the spectrum, so that API does not supply Sakai's
projection `s((r • 1 - h)⁺)`. To avoid claiming a general set-indexed interface or colliding with
future upstream naming, Sak-AI uses `WStarAlgebra.spectralProjectionIio`.

The cutoff `CStarAlgebra.spectralPositivePart` and its norm-continuity theorem are isolated in a
C-star-only module; the W-star module adds only support, projection-order, and ultraweak-convergence
arguments. This split is the current portability decision and needs no human design gate.

## Accepted API review for Sakai 1.14.2

The 2026-09-01 comparison used pinned Mathlib commit `476ab284...`, audited current Mathlib commit
`567908cf...`, original LeanOA commit `cb811c...`, and the pre-transaction Sak-AI tree. No existing
functional-support, GNS-null-left-ideal, or applicable positive-functional faithfulness API was
found.

The accepted public construction is `PositiveLinearMap.support φ hφ`, separate by namespace and
type from `WStarAlgebra.support` for algebra elements. Its explicit
`IsNormalOnProjections` argument is mathematically necessary for the closed-ideal route; the
canonical $W^*$-predual is selected only inside the definition. `PositiveLinearMap.nullIdeal` is
more general and remains at the unital $C^*$-algebra boundary. The exact source orientation is
`x ∈ φ.nullIdeal ↔ x * (φ.support hφ).1 = 0`.

The review rejected a second supremum-based support, a normal-positive-functional bundle, a
`Faithful` predicate, a public null-support object, and a second corner construction. The stable
interface instead reuses the existing closed-left-ideal classifier and `IsStarProjection.Corner`,
and publishes theorem-level greatest-zero, cutdown, full-support, and faithful-corner consequences.
The two Cauchy--Schwarz coefficient-zero lemmas and the ring-theoretic complement-of-idempotent
ideal lemma are recorded as plausible upstream candidates; no new human design gate blocks
Definition 1.14.1 or Theorem 1.14.3.

## Accepted API review for Sakai 1.14.1 and 1.14.3

The 2026-09-01 audit found no matching functional Jordan decomposition or positive-functional
norm-orthogonality API in pinned Mathlib, audited current Mathlib, original LeanOA, or baseline
Sak-AI. Mathlib's `Disjoint` and other `IsOrthogonal` uses do not express Sakai's norm relation.

The accepted source definition is `PositiveLinearMap.IsOrthogonal`, at natural nonunital
$C^*$-algebra generality. For normal positive functionals the structural theorem
`PositiveLinearMap.isOrthogonal_iff_support_mul_eq_zero` is downstream of, rather than a
replacement for, that definition. Its converse is proved after Jordan uniqueness, so the
dependency is acyclic.

The accepted source theorem is
`Ultraweak.existsUnique_orthogonal_decomposition_of_isSelfAdjoint`. It reuses the existing
self-adjoint-unitary positive factorization, returns ordinary positive maps with explicit
`IsNormalOnProjections` proofs, and records the exact norm sum through `IsOrthogonal`. Independent
review confirmed positivity, normality, sign, norm identity, support orientations, uniqueness,
and the predual boundary. The review rejected public choice-based parts, a Jordan-decomposition
structure, a normal-functional wrapper, exposed carrier projections, and a competing polar API.
No human design gate blocks the source audit of Theorem 1.14.4.

## Accepted API review for Sakai 1.14.4

The direct source audit fixes Sakai's convention as
`R_v φ (x) = φ (x * v)`, with `star v * v = s(φ)`, equal norms, uniqueness of both `v` and `φ`,
and `v * star v = s(|g⋆|)`. The previous `Ultraweak.PolarDecomposition` theorem covers only a
self-adjoint functional through a self-adjoint unitary and left multiplication; it is reusable
analytic infrastructure but is not the general source theorem.

The accepted extension is the downstream module
`LeanOA.Ultraweak.FunctionalPolarDecomposition`. Its source-facing endpoint is
`Ultraweak.existsUnique_functional_polar_decomposition`. The ordinary positive conjugation
`PositiveLinearMap.conjugate` is published at nonunital C-star generality, while normality and
support transport reuse the established ultraweak-continuity and functional-support APIs.
`Ultraweak.functionalAbs` is published only after pair uniqueness because Sakai immediately uses
the canonical positive factor as `|g|`.

The review rejected a second functional-polar namespace, a normal-functional wrapper, another
support/carrier construction, and a new `IsPartialIsometry` predicate. The source equation
`star v * v = s(φ)` already provides the established projection-based partial-isometry semantics.
Section 1.14 is complete. No human design gate blocks the Section 1.15 concrete-topology audit.

## Accepted API review for the Sakai 1.15.1 first transaction

The direct source audit establishes that Proposition 1.15.1 is a global closedness theorem for a
self-adjoint, not explicitly unital, subalgebra of $B(H)$ over a complex Hilbert space. Its five
conditions use WOT, $\sigma$-WOT, SOT, Sakai's square-summable-vector “strongest operator topology”
(modern ultrastrong), and $\sigma(B(H),B(H)_*)$. The last two named topologies are not the
strong-star and Mackey topologies, respectively, and the separately defined $\sigma$-WOT must not be
identified with the predual weak topology before the later source corollary proves that equality.

The accepted public additions are deliberately one-way and representation-neutral:
`PointwiseConvergenceCLM.toWOT` gives the canonical continuous identity from Mathlib's
pointwise/SOT realization to its WOT realization, and
`PointwiseConvergenceCLM.isClosed_pointwise_of_isClosed_wot` gives the immediate closedness
consequence at arbitrary normed-field generality. The intrinsic theorem
`Ultraweak.Strong.isClosed_iff_image_toUltraweakEquiv` packages an existing convex closure result
as the reusable closedness equivalence between Sak-AI's two specified-predual synonyms. These
declarations introduce no topology and do not identify a concrete operator topology with an
intrinsic one.

Proposition 1.15.1 is **not source-formalized**. At this first-transaction checkpoint, pinned and
current Mathlib did not supply the concrete predual of $B(H)$ or the missing
$\sigma$-WOT/ultrastrong identifications, and Sak-AI had not yet bridged its intrinsic predual
topology or relative Kaplansky argument to the concrete WOT closure. IQ-010 owns that boundary.
The then-approved next bounded work was the concrete coefficient/predual bridge, with the
proposition kept as the exact source frontier.

## Accepted API review for the Sakai 1.15.1 coefficient-predual transaction

The finite vector-functional span now has its exact norm formula and dense isometric inclusion in
its operator-dual norm closure. Canonical evaluation is an isometry without a completeness
assumption on the Hilbert codomain; completeness enters only for the Fréchet--Riesz recovery that
proves surjectivity. The resulting duality theorem is deliberately general: the operator domain is
only seminormed, while the codomain is a complete Hilbert space over an `RCLike` scalar.

The operator-algebra assembly installs the existing `Predual` class only at the naturally normed
domain boundary. A short carrier is canonically linearly isometric to the actual closure subtype;
this wrapper is an elaboration boundary, not a competing mathematical predual, and fresh-import
probes confirm that direct and opposite predual instances synthesize at the project default. The
duality equivalence uses the explicit Riesz recovery map as its inverse, rather than a
choice-generated inverse.

This infrastructure is accepted and has a Verso node. It is not Sakai Proposition 1.15.1: the
square-summable coefficient-series comparison, concrete ultrastrong comparison, and relative
Kaplansky closure argument remain OPEN / RED under IQ-010. The approved next bounded work is the
coefficient-series API and its one-sided specified-predual topology comparison.
