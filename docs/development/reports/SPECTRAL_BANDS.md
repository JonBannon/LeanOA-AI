# Spectral-band theorem cluster report

## Scope

- Worktree: `/private/tmp/sakai-agent-bands-463d37e`
- Branch: `agent/spectral-bands`
- Baseline: `463d37e86e1de217b65b2976f342db32393b6245`
- Owned Lean module: `LeanOA/Ultraweak/SpectralBand.lean`

This workstream adds theorem-level facts about differences of
`WStarAlgebra.spectralProjectionIio`.  It does not add a spectral-band definition, a bundled
spectral family, a set-indexed projection-valued measure, or an integral interface.

## Overlap audit

The audit covered:

- Sak-AI at the baseline above;
- pinned Mathlib at `476ab284693e554a6b48c5f5210cb4fb5ae51252`;
- Mathlib master at `2ca39e62989124794bd8405bb2e60805f63d37bc`;
- the read-only original LeanOA at `cb811c1006ae78a0ff1d175253200e1859843370`.

Sak-AI already supplies monotonicity and commutation with the original self-adjoint element in
`Ultraweak.SpectralProjection`.  It also already supplies the full finite telescoping identity
`WStarAlgebra.sum_spectralProjectionIio_sub` in `Ultraweak.SpectralSum`; that result was reused as
the established finite-sum endpoint API rather than duplicated here.

Pinned and current Mathlib supply the generic projection results used by the implementation:

- `IsStarProjection.le_iff_sub`;
- `IsStarProjection.le_iff_mul_eq_left`;
- `IsStarProjection.commute_of_le`.

No lower-spectral-projection API or four-projection ordered-difference orthogonality lemma was
found in current Mathlib, and the original LeanOA has no corresponding spectral construction.

## Implemented API

`LeanOA.Ultraweak.SpectralBand` provides:

- `WStarAlgebra.isStarProjection_spectralProjectionIio_sub`;
- `WStarAlgebra.commute_spectralProjectionIio_spectralProjectionIio`;
- `WStarAlgebra.commute_spectralProjectionIio_sub`;
- `WStarAlgebra.commute_spectralProjectionIio_sub_spectralProjectionIio`;
- `WStarAlgebra.commute_spectralProjectionIio_sub_spectralProjectionIio_sub`;
- `WStarAlgebra.spectralProjectionIio_sub_add_sub`;
- `WStarAlgebra.spectralProjectionIio_sub_mul_spectralProjectionIio_sub_eq_zero`.

The projection theorem uses only the ordered-cut hypothesis needed to apply monotonicity.  The
commutation and adjacent-additivity theorems intentionally omit ordering assumptions because those
identities hold for arbitrary cuts.  Orthogonality is stated for two internally ordered bands with
the first ending no later than the second begins.  Its reverse product follows from the public
band-commutation theorem, so no duplicate reverse-orientation theorem was added.

## Declined additions

- A public `spectralBand` definition was not justified: all current consumers use the algebra
  element represented by the literal projection difference, and a wrapper would create a new
  interface before the eventual spectral-resolution design is settled.
- The existing full finite telescoping theorem was not copied into the new module.
- No theorem was marked `simp`; none of the new parameterized rewrites is an unconditional global
  normalization rule.
- No set-indexed or integral structure was introduced, in accordance with IQ-001.

## Integration question: generic four-projection lemma

The ordered-band orthogonality proof factors through the following genuinely generic fact:

```text
p ≤ q ≤ r ≤ s  ⇒  (q - p) * (s - r) = 0
```

for four star projections in a $C^*$-algebra with the usual projection order.  The proof needs
only Mathlib's projection-order multiplication characterizations and ring arithmetic; it has no
spectral or $W^*$-algebra content.  No equivalent declaration was found in pinned or current
Mathlib.

Recommendation: integration should consider extracting this as a small declaration in
`LeanOA/Mathlib/Analysis/CStarAlgebra/Projection.lean`, likely in the `IsStarProjection` namespace,
then shorten the spectral theorem to an application.  This is a natural answer to IQ-002, but the
shared staging file was deliberately not edited under this workstream contract.

## Validation

The following focused command succeeds:

```sh
lake build LeanOA.Ultraweak.SpectralBand
```

The build completed all 3069 jobs, including the new module.  The owned Lean source contains no
proof placeholders.  Public umbrella import and whole-repository lint/build remain integration
tasks because this workstream was expressly forbidden to edit `LeanOA.lean`.
