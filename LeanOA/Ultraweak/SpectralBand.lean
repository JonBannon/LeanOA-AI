module

public import LeanOA.Ultraweak.SpectralProjection

@[expose] public section

/-!
# Spectral bands in a W-star algebra

This file records a small theorem-level API for differences of lower spectral projections.  An
ordered difference
`(spectralProjectionIio a s).1 - (spectralProjectionIio a r).1`, with `r ≤ s`, is again a
projection.
Such differences commute with the original self-adjoint element and with every lower spectral
projection, add over adjacent intervals, and are orthogonal when their intervals are ordered and
disjoint.

No separate spectral-band object or set-indexed spectral measure is introduced.  The full finite
telescoping identity is already available as `WStarAlgebra.sum_spectralProjectionIio_sub` in
`LeanOA.Ultraweak.SpectralSum`.
-/

namespace WStarAlgebra

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] [WStarAlgebra M]

/-- The difference of two ordered lower spectral projections is a star projection. -/
theorem isStarProjection_spectralProjectionIio_sub (a : selfAdjoint M) {r s : ℝ}
    (hrs : r ≤ s) :
    IsStarProjection
      ((spectralProjectionIio a s).1 - (spectralProjectionIio a r).1) :=
  ((spectralProjectionIio a r).2.le_iff_sub (spectralProjectionIio a s).2).mp
    (spectralProjectionIio_mono a hrs)

/-- Any two lower spectral projections of the same self-adjoint element commute. -/
theorem commute_spectralProjectionIio_spectralProjectionIio
    (a : selfAdjoint M) (r s : ℝ) :
    Commute (spectralProjectionIio a r).1 (spectralProjectionIio a s).1 := by
  rcases le_total r s with hrs | hsr
  · exact (spectralProjectionIio a r).2.commute_of_le (spectralProjectionIio a s).2
      (spectralProjectionIio_mono a hrs)
  · exact ((spectralProjectionIio a s).2.commute_of_le (spectralProjectionIio a r).2
      (spectralProjectionIio_mono a hsr)).symm

/-- A self-adjoint element commutes with every difference of two of its lower spectral
projections.  No ordering assumption on the cuts is needed for commutation. -/
theorem commute_spectralProjectionIio_sub (a : selfAdjoint M) (r s : ℝ) :
    Commute a.1
      ((spectralProjectionIio a s).1 - (spectralProjectionIio a r).1) :=
  (commute_spectralProjectionIio a s).sub_right (commute_spectralProjectionIio a r)

/-- Every difference of lower spectral projections commutes with every lower spectral projection
of the same self-adjoint element. -/
theorem commute_spectralProjectionIio_sub_spectralProjectionIio
    (a : selfAdjoint M) (r s t : ℝ) :
    Commute
      ((spectralProjectionIio a s).1 - (spectralProjectionIio a r).1)
      (spectralProjectionIio a t).1 :=
  (commute_spectralProjectionIio_spectralProjectionIio a s t).sub_left
    (commute_spectralProjectionIio_spectralProjectionIio a r t)

/-- Any two differences of lower spectral projections of the same self-adjoint element commute. -/
theorem commute_spectralProjectionIio_sub_spectralProjectionIio_sub
    (a : selfAdjoint M) (r s t u : ℝ) :
    Commute
      ((spectralProjectionIio a s).1 - (spectralProjectionIio a r).1)
      ((spectralProjectionIio a u).1 - (spectralProjectionIio a t).1) :=
  (commute_spectralProjectionIio_sub_spectralProjectionIio a r s u).sub_right
    (commute_spectralProjectionIio_sub_spectralProjectionIio a r s t)

/-- Differences of lower spectral projections are finitely additive over adjacent intervals. -/
theorem spectralProjectionIio_sub_add_sub (a : selfAdjoint M) (r s t : ℝ) :
    ((spectralProjectionIio a s).1 - (spectralProjectionIio a r).1) +
        ((spectralProjectionIio a t).1 - (spectralProjectionIio a s).1) =
      (spectralProjectionIio a t).1 - (spectralProjectionIio a r).1 := by
  abel

/-- Spectral bands on ordered disjoint intervals are orthogonal.  The reverse product also
vanishes by `commute_spectralProjectionIio_sub_spectralProjectionIio_sub`. -/
theorem spectralProjectionIio_sub_mul_spectralProjectionIio_sub_eq_zero
    (a : selfAdjoint M) {r s t u : ℝ} (hrs : r ≤ s) (hst : s ≤ t) (htu : t ≤ u) :
    ((spectralProjectionIio a s).1 - (spectralProjectionIio a r).1) *
        ((spectralProjectionIio a u).1 - (spectralProjectionIio a t).1) = 0 := by
  have hmul {x y : ℝ} (hxy : x ≤ y) :
      (spectralProjectionIio a x).1 * (spectralProjectionIio a y).1 =
        (spectralProjectionIio a x).1 :=
    ((spectralProjectionIio a x).2.le_iff_mul_eq_left
      (spectralProjectionIio a y).2).mp (spectralProjectionIio_mono a hxy)
  rw [mul_sub, sub_mul, sub_mul, hmul (hst.trans htu), hmul hst,
    hmul (hrs.trans (hst.trans htu)), hmul (hrs.trans hst), sub_self]

end WStarAlgebra
