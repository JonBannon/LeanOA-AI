module

public import LeanOA.CStarAlgebra.Spectral
public import LeanOA.Ultraweak.LUB
public import LeanOA.Ultraweak.Support
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

@[expose] public section

/-!
# Spectral projections in a W-star algebra

This file begins the spectral-resolution construction for a self-adjoint element of a W-star
algebra.  The lower spectral projection at `r` is the support of `(r • 1 - a)⁺`; equivalently,
it is the projection associated with the open interval `Set.Iio r`.

The main results are continuity from below and the two-sided spectral-band increment estimate.
These are Sakai, Lemmas 1.11.1 and 1.11.2; continuity is stated for directed nets rather than only
sequences, and the increment estimate allows equal cuts.
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

/-- The lower spectral projection is the support of the literal positive part
`(algebraMap ℝ M r - a)⁺`. -/
theorem spectralProjectionIio_eq_support_posPart (a : selfAdjoint M) (r : ℝ) :
    spectralProjectionIio a r =
      support ⟨(algebraMap ℝ M r - a.1)⁺, (CFC.posPart_nonneg _).isSelfAdjoint⟩ := by
  apply congrArg support
  exact Subtype.ext (CStarAlgebra.spectralPositivePart_eq_posPart a r)

/-- A lower spectral projection acts as a left identity on its defining positive cutoff. -/
@[simp]
theorem spectralProjectionIio_mul_spectralPositivePart (a : selfAdjoint M) (r : ℝ) :
    (spectralProjectionIio a r).1 * CStarAlgebra.spectralPositivePart a r =
      CStarAlgebra.spectralPositivePart a r := by
  exact support_mul ⟨CStarAlgebra.spectralPositivePart a r,
    (CStarAlgebra.spectralPositivePart_nonneg a r).isSelfAdjoint⟩

/-- The positive cutoff defining a lower spectral projection is fixed on the right as well. -/
@[simp]
theorem spectralPositivePart_mul_spectralProjectionIio (a : selfAdjoint M) (r : ℝ) :
    CStarAlgebra.spectralPositivePart a r * (spectralProjectionIio a r).1 =
      CStarAlgebra.spectralPositivePart a r := by
  exact mul_support ⟨CStarAlgebra.spectralPositivePart a r,
    (CStarAlgebra.spectralPositivePart_nonneg a r).isSelfAdjoint⟩

/-- A lower spectral projection acts as a left identity on `(algebraMap ℝ M r - a)⁺`. -/
@[simp]
theorem spectralProjectionIio_mul_posPart (a : selfAdjoint M) (r : ℝ) :
    (spectralProjectionIio a r).1 * (algebraMap ℝ M r - a.1)⁺ =
      (algebraMap ℝ M r - a.1)⁺ := by
  rw [← CStarAlgebra.spectralPositivePart_eq_posPart]
  exact spectralProjectionIio_mul_spectralPositivePart a r

/-- The positive part `(algebraMap ℝ M r - a)⁺` is fixed on the right by its lower spectral
projection. -/
@[simp]
theorem posPart_mul_spectralProjectionIio (a : selfAdjoint M) (r : ℝ) :
    (algebraMap ℝ M r - a.1)⁺ * (spectralProjectionIio a r).1 =
      (algebraMap ℝ M r - a.1)⁺ := by
  rw [← CStarAlgebra.spectralPositivePart_eq_posPart]
  exact spectralPositivePart_mul_spectralProjectionIio a r

/-- The positive cutoff is recovered by restricting its defining scalar translate to the lower
spectral projection. -/
@[simp]
theorem sub_mul_spectralProjectionIio (a : selfAdjoint M) (r : ℝ) :
    (algebraMap ℝ M r - a.1) * (spectralProjectionIio a r).1 =
      CStarAlgebra.spectralPositivePart a r := by
  rw [CStarAlgebra.spectralPositivePart_eq_posPart,
    spectralProjectionIio_eq_support_posPart]
  let x : M := algebraMap ℝ M r - a.1
  have hx : IsSelfAdjoint x :=
    (IsSelfAdjoint.algebraMap M (isSelfAdjoint_iff.mpr (star_trivial r))).sub a.property
  exact mul_support_posPart ⟨x, hx⟩

/-- The right-handed form of the spectral-cut recovery identity. -/
@[simp]
theorem spectralProjectionIio_mul_sub (a : selfAdjoint M) (r : ℝ) :
    (spectralProjectionIio a r).1 * (algebraMap ℝ M r - a.1) =
      CStarAlgebra.spectralPositivePart a r := by
  rw [CStarAlgebra.spectralPositivePart_eq_posPart,
    spectralProjectionIio_eq_support_posPart]
  let x : M := algebraMap ℝ M r - a.1
  have hx : IsSelfAdjoint x :=
    (IsSelfAdjoint.algebraMap M (isSelfAdjoint_iff.mpr (star_trivial r))).sub a.property
  exact support_posPart_mul ⟨x, hx⟩

/-- The scalar translate defining a lower spectral projection commutes with that projection. -/
theorem commute_sub_spectralProjectionIio (a : selfAdjoint M) (r : ℝ) :
    Commute (algebraMap ℝ M r - a.1) (spectralProjectionIio a r).1 := by
  rw [commute_iff_eq, sub_mul_spectralProjectionIio, spectralProjectionIio_mul_sub]

/-- A self-adjoint element commutes with each of its lower spectral projections. -/
theorem commute_spectralProjectionIio (a : selfAdjoint M) (r : ℝ) :
    Commute a.1 (spectralProjectionIio a r).1 := by
  have hscalar : Commute (algebraMap ℝ M r) (spectralProjectionIio a r).1 :=
    Algebra.commutes r _
  have h := hscalar.sub_left (commute_sub_spectralProjectionIio a r)
  simpa only [sub_sub_cancel] using h

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

/-- On the difference of two lower spectral projections, the self-adjoint element lies between
the two scalar cuts.  This is the reusable spectral-band estimate underlying Sakai, Lemma 1.11.2.
-/
theorem spectralProjectionIio_band_bounds (a : selfAdjoint M) {r s : ℝ} (hrs : r ≤ s) :
    r • ((spectralProjectionIio a s).1 - (spectralProjectionIio a r).1) ≤
        a.1 * ((spectralProjectionIio a s).1 - (spectralProjectionIio a r).1) ∧
      a.1 * ((spectralProjectionIio a s).1 - (spectralProjectionIio a r).1) ≤
        s • ((spectralProjectionIio a s).1 - (spectralProjectionIio a r).1) := by
  let er : M := (spectralProjectionIio a r).1
  let es : M := (spectralProjectionIio a s).1
  let p : M := es - er
  have her : IsStarProjection er := (spectralProjectionIio a r).2
  have hes : IsStarProjection es := (spectralProjectionIio a s).2
  have hers : er ≤ es := spectralProjectionIio_mono a hrs
  have hp : IsStarProjection p := (her.le_iff_sub hes).mp hers
  have hap : Commute a.1 p := by
    exact (commute_spectralProjectionIio a s).sub_right
      (commute_spectralProjectionIio a r)
  have hscalar (t : ℝ) : Commute (algebraMap ℝ M t) p := Algebra.commutes t p
  let xr : M := algebraMap ℝ M r - a.1
  let xrPos : selfAdjoint M := ⟨xr⁺, (CFC.posPart_nonneg xr).isSelfAdjoint⟩
  have hxr : IsSelfAdjoint xr :=
    (IsSelfAdjoint.algebraMap M (isSelfAdjoint_iff.mpr (star_trivial r))).sub a.property
  have hxr_p : Commute xr p := (hscalar r).sub_left hap
  have hxrNeg_p : Commute xr⁻ p := by
    rw [CFC.negPart_def, cfcₙ_eq_cfc]
    exact hxr_p.cfc_real _
  have her_support : er = (support xrPos).1 := by
    exact congr_arg Subtype.val (spectralProjectionIio_eq_support_posPart a r)
  have herp : er * p = 0 := by
    change er * (es - er) = 0
    rw [mul_sub, (her.le_iff_mul_eq_left hes).mp hers,
      her.isIdempotentElem.eq, sub_self]
  have hxrPos_p : xr⁺ * p = 0 := by
    apply (support_mul_eq_zero_iff xrPos p).mp
    rw [← her_support]
    exact herp
  have hlower : r • p ≤ a.1 * p := by
    rw [← sub_nonneg]
    have hdiff : a.1 * p - r • p = xr⁻ * p := by
      calc
        a.1 * p - r • p = (a.1 - algebraMap ℝ M r) * p := by
          rw [sub_mul, Algebra.smul_def]
        _ = -(algebraMap ℝ M r - a.1) * p := by rw [neg_sub]
        _ = -xr * p := rfl
        _ = -(xr⁺ - xr⁻) * p := by rw [CFC.posPart_sub_negPart xr hxr]
        _ = xr⁻ * p := by rw [neg_sub, sub_mul, hxrPos_p, sub_zero]
    rw [hdiff]
    exact Commute.mul_nonneg (CFC.negPart_nonneg xr) hp.nonneg hxrNeg_p
  let xs : M := algebraMap ℝ M s - a.1
  let xsPos : selfAdjoint M := ⟨xs⁺, (CFC.posPart_nonneg xs).isSelfAdjoint⟩
  have hxs : IsSelfAdjoint xs :=
    (IsSelfAdjoint.algebraMap M (isSelfAdjoint_iff.mpr (star_trivial s))).sub a.property
  have hxs_p : Commute xs p := (hscalar s).sub_left hap
  have hxsPos_p : Commute xs⁺ p := by
    rw [CFC.posPart_def, cfcₙ_eq_cfc]
    exact hxs_p.cfc_real _
  have hxsNeg_p : Commute xs⁻ p := by
    rw [CFC.negPart_def, cfcₙ_eq_cfc]
    exact hxs_p.cfc_real _
  have hes_support : es = (support xsPos).1 := by
    exact congr_arg Subtype.val (spectralProjectionIio_eq_support_posPart a s)
  have hes_neg : es * xs⁻ = 0 := by
    rw [hes_support]
    exact (support_mul_eq_zero_iff xsPos xs⁻).2 (CFC.posPart_mul_negPart xs)
  have hp_le_es : p ≤ es := by
    exact sub_le_self es her.nonneg
  have hpes : p * es = p := (hp.le_iff_mul_eq_left hes).mp hp_le_es
  have hp_neg : p * xs⁻ = 0 := by
    calc
      p * xs⁻ = (p * es) * xs⁻ := by rw [hpes]
      _ = p * (es * xs⁻) := by rw [mul_assoc]
      _ = 0 := by rw [hes_neg, mul_zero]
  have hxsNeg_p_zero : xs⁻ * p = 0 := hxsNeg_p.eq.trans hp_neg
  have hupper : a.1 * p ≤ s • p := by
    rw [← sub_nonneg]
    have hdiff : s • p - a.1 * p = xs⁺ * p := by
      calc
        s • p - a.1 * p = (algebraMap ℝ M s - a.1) * p := by
          rw [sub_mul, Algebra.smul_def]
        _ = xs * p := rfl
        _ = (xs⁺ - xs⁻) * p := by rw [CFC.posPart_sub_negPart xs hxs]
        _ = xs⁺ * p := by rw [sub_mul, hxsNeg_p_zero, sub_zero]
    rw [hdiff]
    exact Commute.mul_nonneg (CFC.posPart_nonneg xs) hp.nonneg hxsPos_p
  exact ⟨hlower, hupper⟩

/-- Sakai's cutoff expression equals the self-adjoint element restricted to the corresponding
lower spectral projection. -/
theorem smul_spectralProjectionIio_sub_spectralPositivePart
    (a : selfAdjoint M) (r : ℝ) :
    r • (spectralProjectionIio a r).1 - CStarAlgebra.spectralPositivePart a r =
      a.1 * (spectralProjectionIio a r).1 := by
  rw [← sub_mul_spectralProjectionIio a r, Algebra.smul_def]
  noncomm_ring

/-- **Sakai, Lemma 1.11.2.**  The increments of
`r • spectralProjectionIio a r - spectralPositivePart a r` are bounded by the endpoint cuts on
the intervening spectral band.  The formal statement allows equal cuts. -/
theorem spectralProjectionIio_increment_bounds (a : selfAdjoint M) {r s : ℝ} (hrs : r ≤ s) :
    r • ((spectralProjectionIio a s).1 - (spectralProjectionIio a r).1) ≤
        (s • (spectralProjectionIio a s).1 - CStarAlgebra.spectralPositivePart a s) -
          (r • (spectralProjectionIio a r).1 - CStarAlgebra.spectralPositivePart a r) ∧
      (s • (spectralProjectionIio a s).1 - CStarAlgebra.spectralPositivePart a s) -
          (r • (spectralProjectionIio a r).1 - CStarAlgebra.spectralPositivePart a r) ≤
        s • ((spectralProjectionIio a s).1 - (spectralProjectionIio a r).1) := by
  rw [smul_spectralProjectionIio_sub_spectralPositivePart,
    smul_spectralProjectionIio_sub_spectralPositivePart, ← mul_sub]
  exact spectralProjectionIio_band_bounds a hrs

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
