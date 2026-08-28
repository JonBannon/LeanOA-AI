module

public import LeanOA.CFC
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity

@[expose] public section

/-!
# Scalar spectral cutoffs in a C-star algebra

This file develops the positive element `(r • 1 - a)⁺` as a continuous function of the real
cut `r`, for a fixed self-adjoint element `a`.  The construction needs no predual or W-star
structure and is used to construct lower spectral projections in a W-star algebra.
-/

open Filter
open scoped Topology

namespace CStarAlgebra

variable {A : Type*} [CStarAlgebra A]

/-- The positive element used to construct the lower spectral projection of `a` at `r`.

Writing this using the continuous functional calculus makes its dependence on the scalar cut
transparent.  It agrees with `(algebraMap ℝ A r - a)⁺` by
`spectralPositivePart_eq_posPart`.
-/
noncomputable def spectralPositivePart (a : selfAdjoint A) (r : ℝ) : A :=
  cfc (fun x : ℝ ↦ (r - x)⁺) a.1

/-- The functional-calculus description of `spectralPositivePart` agrees with the positive part
of the scalar translate of `a`. -/
theorem spectralPositivePart_eq_posPart (a : selfAdjoint A) (r : ℝ) :
    spectralPositivePart a r = (algebraMap ℝ A r - a.1)⁺ := by
  rw [spectralPositivePart, CFC.posPart_def, cfcₙ_eq_cfc]
  change cfc ((fun x : ℝ ↦ x⁺) ∘ (fun x : ℝ ↦ r - x)) a.1 = _
  rw [cfc_comp (fun x : ℝ ↦ x⁺) (fun x : ℝ ↦ r - x) a.1]
  congr 1
  rw [cfc_sub (fun _ : ℝ ↦ r) (fun x : ℝ ↦ x) a.1 (by fun_prop) (by fun_prop),
    show cfc (fun _ : ℝ ↦ r) a.1 = algebraMap ℝ A r from cfc_const r a.1 a.property,
    show cfc (fun x : ℝ ↦ x) a.1 = a.1 from cfc_id' ℝ a.1 a.property]

variable [PartialOrder A] [StarOrderedRing A]

/-- `spectralPositivePart` is nonnegative. -/
theorem spectralPositivePart_nonneg (a : selfAdjoint A) (r : ℝ) :
    0 ≤ spectralPositivePart a r := by
  rw [spectralPositivePart]
  exact cfc_nonneg fun x _ ↦ posPart_nonneg (r - x)

omit [PartialOrder A] [StarOrderedRing A] in
/-- The positive elements defining lower spectral projections depend continuously on the cut.

This is a fixed-element continuous-functional-calculus result; it does not assert operator
continuity of positive part on arbitrary noncommuting self-adjoint elements.
-/
theorem continuous_spectralPositivePart (a : selfAdjoint A) :
    Continuous (spectralPositivePart a) := by
  rw [continuous_iff_continuousAt]
  intro r
  apply continuousAt_cfc_fun
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [Metric.ball_mem_nhds r hε] with s hs x _
    refine ((lipschitzWith_posPart : LipschitzWith 1 (posPart : ℝ → ℝ)).dist_le_mul
      (r - x) (s - x)).trans_lt ?_
    simpa [Real.dist_eq, abs_sub_comm] using hs
  · filter_upwards [] with s
    fun_prop

end CStarAlgebra
