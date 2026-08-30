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

## Major infrastructure question

- No accepted local set-indexed projection-valued-measure or operator-valued integration interface
  has been identified. Audit pinned and current Mathlib before introducing one. A scalar/vector
  Bochner integral is not automatically the right codomain for W*-algebra-valued spectral
  integration.

## External work already monitored

Root `REVIEW_QUEUE.md` records the authoritative status of Mathlib PRs #42093, #42095, and #42100
and the completed overlap audits for Sections 1.10 and 1.11.1. Do not duplicate or silently update
those conclusions here; append only new evidence with commit/revision identifiers.
