# Canonical truncated-affine recovery worker report

## Scope and result

This workstream implemented one theorem-only production module,
`LeanOA.Ultraweak.TruncatedSpectralSum`.  It introduces no partition structure, spectral-family
structure, projection-valued measure, or integral predicate.  The target is the existing Mathlib
CFC-based object

```text
CStarAlgebra.spectralPositivePart a r = cfc (fun x : ℝ => (r - x)⁺) a.1.
```

The main result is a sharp mesh estimate for the existing tagged sums:

```text
‖taggedSpectralSum a cut (fun i => (r - tag i)⁺) n
    - CStarAlgebra.spectralPositivePart a r‖ ≤ δ.
```

Its assumptions are exactly the existing finite-sum assumptions: every tag lies between its two
cuts, every band width is at most `δ`, and the two endpoint cuts contain the spectrum.  There is
no hypothesis that `r` is a cut, that `r` lies between the endpoint cuts, or that a partition is
refined to insert `r`.

## Public theorem surface

- `norm_taggedSpectralSum_sub_mul_spectralProjectionIio_sub_le` is the reusable partial-interval
  estimate.  It needs no spectral endpoint assumptions and compares a tagged sum to
  `a * (E (cut n) - E (cut 0))`; the explicit assumption `0 ≤ δ` keeps the zero-band case honest.
- `spectralPositivePart_mul_spectralProjectionIio_sub_bounds` bounds the compression of the CFC
  positive part on a single band `[q,s)` by `(r-s)⁺` and `(r-q)⁺`.  Its proof separately treats
  the genuine crossing case `q ≤ r ≤ s`.
- `truncated_affine_endpoint_sums_bound_spectralPositivePart` and
  `truncated_affine_endpoint_sums_bound_taggedSpectralSum` expose the two finite sandwiches.
- `truncated_affine_endpoint_sum_gap_le` compares the truncated-affine endpoint gap with the
  already-landed upper/lower identity-sum gap.
- `norm_truncated_affine_taggedSpectralSum_sub_spectralPositivePart_le` is the sharp finite mesh
  estimate.
- `tendsto_truncated_affine_taggedSpectralSum` gives filter-general norm convergence.
- `tendsto_truncated_affine_taggedSpectralSum_ultraweak` passes that limit through the existing
  continuous norm-to-ultraweak map.
- `tendsto_truncated_affine_taggedSpectralSum_dyadic` specializes to the existing dyadic divisions.

All helpers used only to organize the band case split and the scalar positive-part Lipschitz
estimate remain private.

## Interior-cutoff argument

For `P = E(s) - E(q)`, the proof establishes

```text
(r-s)⁺ P ≤ (r1-a)⁺ P ≤ (r-q)⁺ P.
```

When `s ≤ r`, the existing spectral-band bounds apply to `(r1-a)P`.  When `r ≤ q`, the
compression vanishes.  When `q ≤ r ≤ s`, the proof splits the band at the already-existing
canonical projection `E(r)` inside the argument and bounds the resulting lower sub-band.  It does
not mutate the input partition or pretend that the crossing band is aligned.

Summing the band inequalities brackets the CFC target between the right- and left-endpoint
weighted sums.  The scalar map `x => x⁺` is 1-Lipschitz, so their gap is bounded by the existing
upper/lower spectral-sum gap and hence by the mesh.

## CFC-step comparison

A second scratch route was checked: for a finite orthogonal projection partition summing to one,
the sum of `(r-tag i)⁺`-weighted projections is the positive part of
`r • 1 - ∑ tag i • p i`.  Mathlib's `CFC.posPart_negPart_unique` proves the identity after building
the positive and negative coefficient sums.

That route is mathematically clean but was not published here.  It requires a separate generic
orthogonal-step API and norm continuity of operator positive part, and by itself gives qualitative
convergence.  The direct band route reuses the established Sak-AI order API, gives the requested
partial-interval theorem, handles an interior cutoff explicitly, and preserves the sharp `δ`
estimate.  No new local positive-part operation was introduced.

## Validation

Commands run from the isolated worktree:

```text
lake env lean LeanOA/Ultraweak/TruncatedSpectralSum.lean
lake build LeanOA.Ultraweak.TruncatedSpectralSum
lake lint
```

The direct elaboration and focused build passed without warnings; the focused build completed
3072 jobs.  `lake lint` rebuilt the existing umbrella target (3111 jobs) and passed.  The new
module is deliberately not added to the umbrella in this worker commit, per integration-owner
instructions, so integration must add the import before the final repository-wide lint.

A source scan found no `sorry`, `admit`, or `axiom` in the new module.  No Verso source was edited,
and nothing was pushed.

## Handoff

The module is ready for integration review.  The most important review points are theorem naming,
whether every finite sandwich should remain public, and the umbrella import.  The mathematics does
not depend on either rejected integral predicate from D002 and does not cross the RED arbitrary-
resolution boundary.
