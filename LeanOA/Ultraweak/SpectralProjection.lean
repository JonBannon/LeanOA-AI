module

public import LeanOA.CStarAlgebra.Spectral
public import LeanOA.Ultraweak.LUB
public import LeanOA.Ultraweak.Support

@[expose] public section

/-!
# Spectral projections in a W-star algebra

This file begins the spectral-resolution construction for a self-adjoint element of a W-star
algebra.  The lower spectral projection at `r` is the support of `(r • 1 - a)⁺`; equivalently,
it is the projection associated with the open interval `Set.Iio r`.

The main result is continuity from below: an increasing directed net of cuts converging to `r`
gives a net of lower spectral projections converging ultraweakly to the projection at `r`.  This
is Sakai, Lemma 1.11.1, stated for directed nets rather than only sequences.
-/

open Filter Set
open scoped Topology Ultraweak

namespace WStarAlgebra

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] [WStarAlgebra M]

/-- The lower spectral projection of `a` at `r`, corresponding to the interval `Set.Iio r`.

It is the support projection of `(algebraMap ℝ M r - a)⁺`, as in Sakai's construction of the
spectral resolution.
-/
noncomputable def spectralProjectionIio (a : selfAdjoint M) (r : ℝ) :
    {p : M // IsStarProjection p} :=
  support ⟨CStarAlgebra.spectralPositivePart a r,
    (CStarAlgebra.spectralPositivePart_nonneg a r).isSelfAdjoint⟩

/-- A lower spectral projection is the least projection acting as a left identity on the
corresponding positive part. -/
theorem spectralProjectionIio_le_iff (a : selfAdjoint M) (r : ℝ)
    (p : {p : M // IsStarProjection p}) :
    spectralProjectionIio a r ≤ p ↔
      p.1 * CStarAlgebra.spectralPositivePart a r = CStarAlgebra.spectralPositivePart a r :=
  leftSupport_le_iff _ _

/-- Lower spectral projections are monotone in the cut. -/
theorem spectralProjectionIio_mono (a : selfAdjoint M) :
    Monotone (spectralProjectionIio a) := by
  intro r s hrs
  apply leftSupport_mono_of_nonneg (CStarAlgebra.spectralPositivePart_nonneg a r)
  change cfc (fun x : ℝ ↦ (r - x)⁺) a.1 ≤ cfc (fun x : ℝ ↦ (s - x)⁺) a.1
  apply cfc_mono (hf := by fun_prop) (hg := by fun_prop)
  intro x _
  exact posPart_mono (sub_le_sub_right hrs x)

/-- If an increasing directed net of real cuts converges to `r`, the projection at `r` is the
least upper bound of the corresponding lower spectral projections. -/
theorem isLUB_range_spectralProjectionIio_of_tendsto
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (a : selfAdjoint M) {f : I → ℝ} {r : ℝ} (hf : Monotone f)
    (hfr : Tendsto f atTop (𝓝 r)) :
    IsLUB (range fun i ↦ spectralProjectionIio a (f i)) (spectralProjectionIio a r) := by
  constructor
  · rintro p ⟨i, rfl⟩
    exact spectralProjectionIio_mono a (hf.ge_of_tendsto hfr i)
  · intro p hp
    rw [spectralProjectionIio_le_iff]
    have hpos : Tendsto (fun i ↦ CStarAlgebra.spectralPositivePart a (f i)) atTop
        (𝓝 (CStarAlgebra.spectralPositivePart a r)) :=
      (CStarAlgebra.continuous_spectralPositivePart a).continuousAt.tendsto.comp hfr
    have hmul : Tendsto (fun i ↦ p.1 * CStarAlgebra.spectralPositivePart a (f i)) atTop
        (𝓝 (p.1 * CStarAlgebra.spectralPositivePart a r)) := tendsto_const_nhds.mul hpos
    have heq : (fun i ↦ p.1 * CStarAlgebra.spectralPositivePart a (f i)) =
        fun i ↦ CStarAlgebra.spectralPositivePart a (f i) := by
      funext i
      exact (spectralProjectionIio_le_iff a (f i) p).mp (hp ⟨i, rfl⟩)
    rw [heq] at hmul
    exact tendsto_nhds_unique hmul hpos

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P]
  [Predual ℂ M P]

/-- **Continuity from below for lower spectral projections** (Sakai, Lemma 1.11.1).

This directed-net formulation specializes to every increasing real sequence converging to `r`.
-/
theorem tendsto_spectralProjectionIio_of_monotone
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (a : selfAdjoint M) {f : I → ℝ} {r : ℝ} (hf : Monotone f)
    (hfr : Tendsto f atTop (𝓝 r)) :
    Tendsto (fun i ↦ toUltraweak ℂ P (spectralProjectionIio a (f i)).1) atTop
      (𝓝 (toUltraweak ℂ P (spectralProjectionIio a r).1)) := by
  apply tendsto_atTop_isLUB
  · exact Ultraweak.monotone_toUltraweak.comp ((spectralProjectionIio_mono a).comp hf)
  · have hLUB := isLUB_range_spectralProjectionIio_of_tendsto a hf hfr
    have hmono : Monotone (fun i ↦ spectralProjectionIio a (f i)) :=
      (spectralProjectionIio_mono a).comp hf
    have hLUBM : IsLUB
        (range fun i ↦ (spectralProjectionIio a (f i)).1)
        (spectralProjectionIio a r).1 := by
      simpa only [← range_comp', Function.comp_apply] using
        IsStarProjection.isLUB_coe_of_isLUB P _ hmono.directed_le.directedOn_range
          (range_nonempty _) hLUB
    constructor
    · rintro q ⟨i, rfl⟩
      exact Ultraweak.monotone_toUltraweak (hLUBM.1 ⟨i, rfl⟩)
    · intro q hq
      rw [← toUltraweak_ofUltraweak (𝕜 := ℂ) (m := q)]
      exact Ultraweak.monotone_toUltraweak <| hLUBM.2 fun p hp ↦ by
        obtain ⟨i, rfl⟩ := hp
        exact Ultraweak.monotone_ofUltraweak (hq ⟨i, rfl⟩)

end WStarAlgebra
