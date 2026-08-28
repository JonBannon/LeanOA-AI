# Sak-AI human review queue and upstream opportunities

Last updated: 2026-08-27

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
