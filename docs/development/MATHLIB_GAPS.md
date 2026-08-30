# Mathlib overlap and gap log

This is an API-reconnaissance log, not a commitment to upstream every helper.

## Already exists — reuse it

- Mathlib's native `TwoSidedIdeal` is the accepted Sak-AI representation.
- `IsStarProjection.le_iff_sub` supplies projection differences from order; do not re-prove the
  general result in Sak-AI.
- Mathlib's continuous functional calculus, self-adjoint subtype, and GNS construction are the
  foundations for the current C*-algebra and representation work.
- Standard filters, finite sums, and normed-space integration should be reused wherever their
  codomain assumptions fit; the spectral audit must determine where they stop fitting.

## Local helpers / plausible upstream candidates

- `IsStarProjection.mul_eq_self_of_nonneg_of_le_of_mul_eq_self` is a general hereditary-support
  lemma already isolated in the mirrored Mathlib hierarchy.
- The semiring-level annihilator lemmas may be upstreamable independently of the unresolved
  `TwoSidedIdeal` representation question.
- Generic weak-bilinear transport and compatibility lemmas should be compared to current Mathlib
  before further local expansion.
- Current Mathlib master contains `IsSelfAdjoint.norm_le_max_of_le_of_le`, but it is not an exact
  drop-in replacement for the pinned local declaration in `LeanOA/CFC.lean`: upstream assumes the
  middle element is self-adjoint, while the local signature derives that fact from a self-adjoint
  lower bound. On the next Mathlib update, remove the local duplicate and make the middle
  self-adjointness explicit at consumers such as tagged spectral sums.

## Major infrastructure question

- No accepted local set-indexed projection-valued-measure or operator-valued integration interface
  has been identified. Audit pinned and current Mathlib before introducing one. A scalar/vector
  Bochner integral is not automatically the right codomain for W*-algebra-valued spectral
  integration.

The completed audit in `reports/MATHLIB_SPECTRAL_AUDIT.md` distinguishes the layers precisely:
`VectorMeasure` can express topology-parametric additivity, but its integral uses norm variation;
current `Archive/RiemannStieltjes.lean` is likewise norm-topological and is neither pinned nor a
general PVM. The current shortest route is therefore theorem-level ultraweak tagged-sum limits,
not a local operator-valued measure.

## Spectral-integral interface experiment

D002 adds a narrower conclusion. At current-Mathlib commit `2ca39e6`,
`Archive/RiemannStieltjes.lean` is a useful design precedent: its named integral predicate is a
thin wrapper around `BoxIntegral.HasIntegral` only because `BoxIntegral` already owns tagged boxes,
Riemann/Henstock gauges, filter bases, eventual partition results, and a non-bottom theorem. It is
not a usable dependency for Sak-AI because it is absent from pinned Mathlib, norm-topological,
box-based, and its Riemann wrapper is mesh-only.

The endpoint geometry also needs an explicit adapter: Sak-AI's difference of two `Iio` spectral
projections represents `[r,s)`, whereas the box increment infrastructure is organized around its
own box convention. `Finpartition` provides refinement but not tags, ordered real endpoints, mesh,
or atom ownership. `SimpleFunc` does not remove the gap because spectral integration of its fibers
already requires a set-indexed projection assignment.

The scratch proofs further show that an abstract non-bottom canonical filter is not the missing
Mathlib object: after it is built, the proposed generic predicate is exactly `Tendsto`. The missing
content is the integrator's projection/additivity/continuity laws and honest treatment of atoms.
For the next continuous truncated-affine consumer, reuse generic `Tendsto` and the existing
norm-to-ultraweak map rather than adding a local integration hierarchy.

## First-wave general helper

- `IsStarProjection.sub_mul_sub_eq_zero_of_le` is a plausible Mathlib contribution: it is stated
  for nonunital $C^*$-algebras and says that differences from two ordered disjoint intervals in a
  chain of four projections are orthogonal. No equivalent was found in pinned or current Mathlib.

## External work already monitored

Root `REVIEW_QUEUE.md` records the authoritative status of Mathlib PRs #42093, #42095, and #42100
and the completed overlap audits for Sections 1.10 and 1.11.1. Do not duplicate or silently update
those conclusions here; append only new evidence with commit/revision identifiers.
