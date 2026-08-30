# Tagged spectral sums workstream report

## Scope

This workstream designed the smallest tagged finite-sum layer over the GREEN
`WStarAlgebra.spectralProjectionIio`, `lowerSpectralSum`, `upperSpectralSum`, and dyadic
approximation APIs. It does not introduce a partition type, projection-valued measure, spectral
integral, or bundled generic projection family.

## Overlap audit

Searches covered the Sak-AI source tree, pinned Mathlib at `476ab284693e554a6b48c5f5210cb4fb5ae51252`,
the locally available `origin/master` Mathlib ref at `f988eda5de1aff03157c116b01178564a2ad1c01`,
and Jireh Loreaux's read-only LeanOA checkout at `cb811c1006ae78a0ff1d175253200e1859843370`.
No tagged spectral-sum construction or theorem was found.

The norm argument reuses `IsSelfAdjoint.norm_le_max_of_le_of_le` from Sak-AI's existing `CFC` API
rather than reproving a general order-interval estimate. Current Mathlib master contains a theorem
with the same mathematical role but a different self-adjointness hypothesis; this confirms the
abstraction boundary while requiring a small migration when the dependency is updated.

## Integrated API

- `WStarAlgebra.taggedSpectralSum`
- `WStarAlgebra.taggedSpectralSum_eq_lowerSpectralSum`
- `WStarAlgebra.taggedSpectralSum_eq_upperSpectralSum`
- `WStarAlgebra.isSelfAdjoint_taggedSpectralSum`
- `WStarAlgebra.lowerSpectralSum_le_taggedSpectralSum`
- `WStarAlgebra.taggedSpectralSum_le_upperSpectralSum`
- `WStarAlgebra.lowerSpectralSum_le_taggedSpectralSum_and_taggedSpectralSum_le_upperSpectralSum`
- `WStarAlgebra.norm_taggedSpectralSum_sub_self_le_norm_upperSpectralSum_sub_lowerSpectralSum`
- `WStarAlgebra.norm_taggedSpectralSum_sub_self_le`
- `WStarAlgebra.tendsto_taggedSpectralSum`
- `WStarAlgebra.tendsto_taggedSpectralSum_ultraweak`
- `WStarAlgebra.tendsto_taggedSpectralSum_dyadic`

The one-sided sandwich theorems assume cut monotonicity separately, which is mathematically
necessary to make every spectral-band difference nonnegative. The combined sandwich and all later
results instead assume that every tag lies between its adjacent cuts; this condition already
implies cut monotonicity and avoids a redundant public hypothesis.

## Generality decision

The finite-sum definition remains specialized to `spectralProjectionIio`, because this is its actual
consumer and a generic bundled spectral-family object is explicitly out of scope. The analytic
order-interval step is handled by the already generic
`IsSelfAdjoint.norm_le_max_of_le_of_le`. No generic helper is added in the wrong module merely to
shorten the specialized proof.

## Deliberate omissions

- No measure, projection-valued measure, Radon–Stieltjes integral, or operator-valued integral is
  defined. Tagged-sum convergence is only a prerequisite for Sakai's spectral-integral
  representation and is not labeled as that theorem.
- No midpoint-tag definition is added. The filtered and dyadic theorems cover arbitrary admissible
  tags and therefore subsume midpoint choices without enlarging the API.
- No refinement monotonicity theorem is asserted: arbitrary tags do not make tagged sums monotone
  under refinement.
- No separate dyadic ultraweak theorem is duplicated. A single filter-general ultraweak corollary
  is named because it makes Sakai's source topology explicit; its proof only passes the stronger
  norm limit through the existing canonical continuous map.

## Validation status

The worker's isolated-worktree write was blocked by the environment's repository safety guard due
to an earlier APAIOA-only isolation instruction. In accordance with the guard, no workaround was
used. The lead integrator applied the proposal in the authorized Sak-AI checkout, added canonical
bridges back to the existing lower and upper sums, and validated the integrated module.

Integration validation:

```sh
lake build LeanOA.Ultraweak.TaggedSpectralSum
rg -n "sorry|admit" LeanOA/Ultraweak/TaggedSpectralSum.lean
lake build
lake lint
```

## Integration outcomes

1. The long gap-estimate name was retained because it distinguishes the intermediate gap bound
   from the mesh bound and follows surrounding naming practice.
2. When Sak-AI updates to a Mathlib revision containing upstream
   `IsSelfAdjoint.norm_le_max_of_le_of_le`, the local duplicate in `LeanOA/CFC.lean` should be
   removed through the normal Mathlib-overlap migration. The upstream declaration assumes the
   middle element is self-adjoint, whereas the pinned local declaration derives this from a
   self-adjoint lower bound, so the tagged gap proof will need an explicit middle-element fact.
