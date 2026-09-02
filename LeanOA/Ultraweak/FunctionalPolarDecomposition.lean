module

public import LeanOA.Ultraweak.FunctionalSupport

import LeanOA.CStarAlgebra.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.LocallyConvex.WeakDual

@[expose] public section

/-!
# Polar decomposition of normal functionals

This file formalizes Sakai, Theorem 1.14.4.  A normal functional `g` has a unique
factorization `g x = φ (x * v)` by a normal positive functional `φ` and an element `v` whose
initial projection is the support of `φ`.  The factorization preserves the norm.  The canonical
positive factor is exposed as `Ultraweak.functionalAbs`; the support of the corresponding factor
for the adjoint functional is the final projection `v * star v`.

No separate partial-isometry predicate is needed: the equation
`star v * v = (φ.support hφ).1` says precisely that the initial projection is a projection and
therefore supplies the established partial-isometry semantics.
-/

open Metric Set
open scoped ComplexOrder ComplexStarModule Ultraweak

namespace PositiveLinearMap

/-- If `v⋆ * v` is the support of a normal positive functional `φ`, then conjugation by `v`
transports that support to the final projection `v * v⋆`. -/
theorem support_conjugate_eq_mul_star
    {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] [WStarAlgebra M]
    (φ : M →ₚ[ℂ] ℂ) (hφ : φ.IsNormalOnProjections) (v : M)
    (hv : star v * v = (φ.support hφ).1) :
    ((φ.conjugate v).support
      (hφ.conjugate (P := WStarAlgebra.predual M) v)).1 = v * star v := by
  let q : M := (φ.support hφ).1
  let p : M := v * star v
  let ψ : M →ₚ[ℂ] ℂ := φ.conjugate v
  let hψ : ψ.IsNormalOnProjections :=
    hφ.conjugate (P := WStarAlgebra.predual M) v
  let s : M := (ψ.support hψ).1
  have hq : IsStarProjection q := (φ.support hφ).2
  have hi : IsStarProjection (star v * v) := hv.symm ▸ hq
  have hp : IsStarProjection p := by
    simpa only [star_star, p] using hi.mul_star_self
  have hs : IsStarProjection s := (ψ.support hψ).2
  have hvq : v * q = v := by
    dsimp only [q]
    rw [← hv]
    exact hi.mul_star_mul_self_assoc
  have hstar_v_p_v : star v * p * v = q := by
    calc
      star v * p * v = (star v * v) * (star v * v) := by
        simp only [p, mul_assoc]
      _ = q * q := by rw [hv]
      _ = q := hq.isIdempotentElem.eq
  have hψp : ψ p = ψ 1 := by
    change φ (star v * p * v) = φ (star v * 1 * v)
    rw [hstar_v_p_v, mul_one, hv]
  have hsupport_le_p : (ψ.support hψ).1 ≤ p :=
    (ψ.support_le_iff_apply_eq_apply_one hψ ⟨p, hp⟩).2 hψp
  have hψ_complement : ψ (1 - s) = 0 := by
    simpa only [mul_one] using ψ.apply_one_sub_support_mul hψ 1
  let y : M := (1 - s) * v
  have hstar_y_mul_y : star y * y = star v * (1 - s) * v := by
    simp only [y, star_mul, hs.one_sub.isSelfAdjoint.star_eq, mul_assoc]
    rw [← mul_assoc (1 - s) (1 - s) v, hs.one_sub.isIdempotentElem.eq]
  have hφ_y : φ (star y * y) = 0 := by
    rw [hstar_y_mul_y]
    exact hψ_complement
  have hyq : y * q = 0 :=
    (φ.apply_star_mul_self_eq_zero_iff_mul_support_eq_zero hφ y).1 hφ_y
  have hy : y = 0 := by
    calc
      y = y * q := by simp only [y, mul_assoc, hvq]
      _ = 0 := hyq
  have hsv : s * v = v := by
    have hsub : v - s * v = 0 := by
      simpa only [y, sub_mul, one_mul] using hy
    exact (sub_eq_zero.mp hsub).symm
  have hsp : s * p = p := by
    calc
      s * p = (s * v) * star v := by simp only [p, mul_assoc]
      _ = p := by rw [hsv]
  have hp_le_support : p ≤ (ψ.support hψ).1 :=
    (hp.le_iff_mul_eq_right hs).2 hsp
  exact le_antisymm hsupport_le_p hp_le_support

end PositiveLinearMap

namespace Ultraweak

noncomputable section

private lemma exists_norm_le_norm_apply_re_eq_norm_apply
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    (f : E →L[ℂ] ℂ) (x : E) :
    ∃ a : E, ‖a‖ ≤ ‖x‖ ∧ (f a).re = ‖f x‖ := by
  by_cases hx : f x = 0
  · exact ⟨0, by simp, by simp [hx]⟩
  let c : ℂ := star (f x) / ‖f x‖
  refine ⟨c • x, ?_, ?_⟩
  · rw [norm_smul, show c = star (f x) / ‖f x‖ by rfl, norm_div, norm_star,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
      div_self (norm_ne_zero_iff.mpr hx), one_mul]
  · have hphase : star (f x) / ‖f x‖ * f x = (‖f x‖ : ℂ) := by
      rw [RCLike.star_def, div_mul_eq_mul_div, ← Complex.normSq_eq_conj_mul_self,
        Complex.normSq_eq_norm_sq]
      push_cast
      field_simp [norm_ne_zero_iff.mpr hx]
    rw [map_smul, smul_eq_mul, show c = star (f x) / ‖f x‖ by rfl, hphase]
    simp

private theorem exists_extreme_positive_right_factor
    {M P : Type*} [CStarAlgebra M] [Nontrivial M] [PartialOrder M] [StarOrderedRing M]
    [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]
    (g : σ(M, P) →L[ℂ] ℂ) :
    ∃ (u : M) (φ : σ(M, P) →P[ℂ] ℂ),
      u ∈ extremePoints ℝ (closedBall 0 1) ∧
      φ.toContinuousLinearMap = g.comp (mulRightL (P := P) u) ∧
      ‖g.comp (toUltraweakL ℂ M P)‖ =
        ‖(φ.comp (toUltraweakPosCLM P)).toContinuousLinearMap‖ := by
  letI : ContinuousSMul ℝ σ(M, P) := ⟨by
    have hsmul : Continuous fun p : ℂ × σ(M, P) ↦ p.1 • p.2 := continuous_smul
    convert hsmul.comp
      ((Complex.continuous_ofReal.comp continuous_fst).prodMk continuous_snd) using 1
    ext x
    exact RCLike.real_smul_eq_coe_smul (K := ℂ) x.1 x.2⟩
  letI : LocallyConvexSpace ℂ σ(M, P) := Ultraweak.locallyConvexSpace ℂ M P
  letI : LocallyConvexSpace ℝ σ(M, P) :=
    LocallyConvexSpace.to_real ℂ σ(M, P) inferInstance
  let gM : M →L[ℂ] ℂ := g.comp (toUltraweakPosCLM P).toContinuousLinearMap
  let S : Set σ(M, P) := ofUltraweak ⁻¹' closedBall (0 : M) 1
  have hS : IsCompact S := isCompact_closedBall ℂ P (0 : M) 1
  let gr : σ(M, P) →L[ℝ] ℝ := RCLike.reCLM.comp (g.restrictScalars ℝ)
  let K := gr.toExposed S
  obtain ⟨z, hzS, hz⟩ := hS.exists_isMaxOn
    (show S.Nonempty from ⟨0, by simp [S]⟩) gr.continuous.continuousOn
  have hK : IsCompact K := ContinuousLinearMap.toExposed.isExposed.isCompact hS
  obtain ⟨uσ, huK⟩ := hK.extremePoints_nonempty ⟨z, hzS, hz⟩
  have huS : uσ ∈ extremePoints ℝ S :=
    ContinuousLinearMap.toExposed.isExposed.isExtreme.extremePoints_subset_extremePoints huK
  let e := (linearEquiv ℂ M P).restrictScalars ℝ
  have heS : e '' S = closedBall (0 : M) 1 := by
    ext x
    simp only [mem_image, mem_preimage, S]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [e] using hy
    · intro hx
      refine ⟨toUltraweak ℂ P x, ?_, by simp [e]⟩
      simpa using hx
  let u := ofUltraweak uσ
  have huM : u ∈ extremePoints ℝ (closedBall (0 : M) 1) := by
    rw [← heS, ← image_extremePoints]
    exact ⟨uσ, huS, by simp [e, u]⟩
  have huMax : ∀ y ∈ S, gr y ≤ gr uσ := huK.1.2
  have hunit (x : M) (hx : ‖x‖ ≤ 1) : ‖gM x‖ ≤ (gM u).re := by
    obtain ⟨a, han, haf⟩ := exists_norm_le_norm_apply_re_eq_norm_apply gM x
    rw [← haf]
    exact huMax (toUltraweak ℂ P a) <| by
      simpa [S, mem_closedBall_zero_iff] using han.trans hx
  have hB : 0 ≤ (gM u).re := by simpa using hunit 0 (by simp)
  have hgMnorm_le : ‖gM‖ ≤ (gM u).re :=
    gM.opNorm_le_of_unit_norm hB fun x hx ↦ hunit x hx.le
  have hu_norm : ‖u‖ ≤ 1 := by
    simpa [mem_closedBall_zero_iff] using huM.1
  have hgu_re_le : (gM u).re ≤ ‖gM‖ := by
    calc
      (gM u).re ≤ ‖gM u‖ := Complex.re_le_norm _
      _ ≤ ‖gM‖ * ‖u‖ := gM.le_opNorm u
      _ ≤ ‖gM‖ * 1 := mul_le_mul_of_nonneg_left hu_norm (norm_nonneg _)
      _ = ‖gM‖ := mul_one _
  have hgu_re : (gM u).re = ‖gM u‖ := by
    apply le_antisymm (Complex.re_le_norm _)
    exact hunit u hu_norm
  have hgu_nonneg : 0 ≤ gM u := Complex.re_eq_norm.mp hgu_re
  have hgu : (‖gM‖ : ℂ) = gM u := by
    apply Complex.ext
    · simpa using le_antisymm hgMnorm_le hgu_re_le
    · simp [Complex.nonneg_iff.mp hgu_nonneg |>.2]
  let φc : σ(M, P) →L[ℂ] ℂ := g.comp (mulRightL (P := P) u)
  let φM : M →L[ℂ] ℂ := φc.comp (toUltraweakPosCLM P).toContinuousLinearMap
  have hφM_norm_le : ‖φM‖ ≤ ‖gM‖ := by
    refine φM.opNorm_le_bound (norm_nonneg _) fun x ↦ ?_
    calc
      ‖φM x‖ = ‖gM (x * u)‖ := rfl
      _ ≤ ‖gM‖ * ‖x * u‖ := gM.le_opNorm _
      _ ≤ ‖gM‖ * ‖x‖ := by
        gcongr
        calc
          ‖x * u‖ ≤ ‖x‖ * ‖u‖ := norm_mul_le x u
          _ ≤ ‖x‖ * 1 := mul_le_mul_of_nonneg_left hu_norm (norm_nonneg x)
          _ = ‖x‖ := mul_one _
  have hφM_one : φM 1 = (‖gM‖ : ℂ) := by
    simpa [φM, φc, gM] using hgu.symm
  have hφM_norm_ge : ‖gM‖ ≤ ‖φM‖ := by
    calc
      ‖gM‖ = ‖φM 1‖ := by rw [hφM_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg _)]
      _ ≤ ‖φM‖ * ‖(1 : M)‖ := φM.le_opNorm 1
      _ = ‖φM‖ := by simp
  have hφM_norm : (‖φM‖ : ℂ) = φM 1 := by
    rw [hφM_one]
    exact_mod_cast le_antisymm hφM_norm_le hφM_norm_ge
  have hφM_mono : Monotone φM :=
    ContinuousLinearMap.monotone_iff_opNorm_eq_map_one.mpr hφM_norm
  let φ : σ(M, P) →P[ℂ] ℂ := PositiveContinuousLinearMap.mk₀ φc fun x hx ↦ by
    change 0 ≤ φM (ofUltraweak x)
    exact (monotone_iff_map_nonneg φM).mp hφM_mono _ <| ofUltraweak_nonneg.mpr hx
  refine ⟨u, φ, huM, rfl, ?_⟩
  change ‖gM‖ = ‖φM‖
  exact le_antisymm hφM_norm_ge hφM_norm_le

private lemma apply_mul_one_sub_final_eq_zero
    {A : Type*} [CStarAlgebra A] (f : A →L[ℂ] ℂ) (w x : A)
    (hw : IsStarProjection (star w * w))
    (hfw : f (star w) = (‖f‖ : ℂ)) :
    f (x * (1 - w * star w)) = 0 := by
  let p : A := w * star w
  have hp : IsStarProjection p := hw.mul_star_self
  let y : A := x * (1 - p)
  by_contra hy
  have hfy_pos : 0 < ‖f y‖ := norm_pos_iff.mpr hy
  have hf_ne : f ≠ 0 := by
    intro hf
    rw [hf, zero_apply] at hy
    exact hy rfl
  have hf_pos : 0 < ‖f‖ := norm_pos_iff.mpr hf_ne
  let c : ℂ := star (f y) / ‖f y‖
  let z : A := c • y
  have hc_norm : ‖c‖ = 1 := by
    rw [show c = star (f y) / ‖f y‖ by rfl, norm_div, norm_star,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
      div_self (norm_ne_zero_iff.mpr hy)]
  have hfz : f z = (‖f y‖ : ℂ) := by
    have hphase : star (f y) / ‖f y‖ * f y = (‖f y‖ : ℂ) := by
      rw [RCLike.star_def, div_mul_eq_mul_div, ← Complex.normSq_eq_conj_mul_self,
        Complex.normSq_eq_norm_sq]
      push_cast
      field_simp [norm_ne_zero_iff.mpr hy]
    rw [show z = c • y by rfl, map_smul, smul_eq_mul,
      show c = star (f y) / ‖f y‖ by rfl, hphase]
  have hz_norm : ‖z‖ = ‖y‖ := by rw [show z = c • y by rfl, norm_smul, hc_norm, one_mul]
  have hstarw_p : star w * p = star w := by
    have hp' : IsStarProjection (star (star w) * star w) := by
      simpa only [star_star, p] using hp
    simpa only [p, star_star] using hp'.mul_star_mul_self_assoc
  have hstarw_one_sub_p : star w * (1 - p) = 0 := by
    rw [mul_sub, mul_one, hstarw_p, sub_self]
  have hcross (n : ℕ) :
      (n : ℂ) • star w * star z = 0 := by
    have hzstar : star z = star c • ((1 - p) * star x) := by
      simp only [z, y, star_smul, star_mul, hp.one_sub.isSelfAdjoint.star_eq]
    rw [hzstar]
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, ← mul_assoc,
      hstarw_one_sub_p, zero_mul, smul_zero]
  have hw_norm : ‖w‖ ≤ 1 := by
    rw [← sq_le_one_iff₀ (norm_nonneg w), sq, ← CStarRing.norm_star_mul_self]
    exact IsStarProjection.norm_le _ hw
  obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (‖f‖ * ‖y‖ ^ 2 / (2 * ‖f y‖))
  have hn' : ‖f‖ * ‖y‖ ^ 2 < (n : ℝ) * (2 * ‖f y‖) := by
    exact (div_lt_iff₀ (by positivity : 0 < 2 * ‖f y‖)).mp hn
  have hn'' : ‖f‖ ^ 2 * ‖y‖ ^ 2 < 2 * (n : ℝ) * ‖f‖ * ‖f y‖ := by
    have := mul_lt_mul_of_pos_left hn' hf_pos
    nlinarith
  let a : A := (n : ℂ) • star w + z
  have ha_norm : ‖a‖ ≤ √((n : ℝ) ^ 2 + ‖y‖ ^ 2) := by
    calc
      ‖a‖ ≤ √(‖(n : ℂ) • star w‖ ^ 2 + ‖z‖ ^ 2) :=
        CStarRing.norm_add_le_sqrt_of_mul_star_eq_zero (hcross n)
      _ ≤ √((n : ℝ) ^ 2 + ‖y‖ ^ 2) := by
        gcongr
        · rw [norm_smul, norm_star, Complex.norm_natCast]
          exact mul_le_of_le_one_right (Nat.cast_nonneg n) hw_norm
        · exact hz_norm.le
  have ha_norm_sq : ‖a‖ ^ 2 ≤ (n : ℝ) ^ 2 + ‖y‖ ^ 2 := by
    have hs : 0 ≤ (n : ℝ) ^ 2 + ‖y‖ ^ 2 := by positivity
    nlinarith [Real.sq_sqrt hs, norm_nonneg a, Real.sqrt_nonneg ((n : ℝ) ^ 2 + ‖y‖ ^ 2)]
  have hfa : f a = ((n : ℝ) * ‖f‖ + ‖f y‖ : ℝ) := by
    simp only [a, map_add, map_smul, hfw, hfz]
    push_cast
    rfl
  have hfa_norm : ‖f a‖ = (n : ℝ) * ‖f‖ + ‖f y‖ := by
    rw [hfa, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (add_nonneg (mul_nonneg (Nat.cast_nonneg n) (norm_nonneg f))
        (norm_nonneg (f y)))]
  have hop : (n : ℝ) * ‖f‖ + ‖f y‖ ≤ ‖f‖ * ‖a‖ := by
    rw [← hfa_norm]
    exact f.le_opNorm a
  have hsquare : ((n : ℝ) * ‖f‖ + ‖f y‖) ^ 2 ≤
      ‖f‖ ^ 2 * ((n : ℝ) ^ 2 + ‖y‖ ^ 2) := by
    calc
      ((n : ℝ) * ‖f‖ + ‖f y‖) ^ 2 ≤ (‖f‖ * ‖a‖) ^ 2 := by
        rw [pow_two, pow_two]
        exact mul_self_le_mul_self (by positivity) hop
      _ = ‖f‖ ^ 2 * ‖a‖ ^ 2 := by ring
      _ ≤ ‖f‖ ^ 2 * ((n : ℝ) ^ 2 + ‖y‖ ^ 2) := by
        exact mul_le_mul_of_nonneg_left ha_norm_sq (sq_nonneg ‖f‖)
  nlinarith [sq_pos_of_pos hfy_pos]

private theorem exists_functional_polar_decomposition
    {M P : Type*} [CStarAlgebra M] [Nontrivial M] [PartialOrder M] [StarOrderedRing M]
    [WStarAlgebra M]
    [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]
    (g : σ(M, P) →L[ℂ] ℂ) :
    ∃ (v : M) (φ : M →ₚ[ℂ] ℂ) (hφ : φ.IsNormalOnProjections),
      g.comp (toUltraweakL ℂ M P) = φ.cutoff v ∧
        ‖g.comp (toUltraweakL ℂ M P)‖ = ‖φ.toContinuousLinearMap‖ ∧
        star v * v = (φ.support hφ).1 := by
  obtain ⟨u, φσ, hu, hφσ, hnorm⟩ := exists_extreme_positive_right_factor g
  let gM : M →L[ℂ] ℂ := g.comp (toUltraweakL ℂ M P)
  let φ : M →ₚ[ℂ] ℂ :=
    (φσ.comp (toUltraweakPosCLM P)).toPositiveLinearMap
  have hφ : φ.IsNormalOnProjections :=
    PositiveContinuousLinearMap.comp_toUltraweakPosCLM_isNormalOnProjections φσ
  have hu_initial : IsStarProjection (star u * u) :=
    isStarProjection_star_mul_self_of_mem_extremePoints_unitClosedBall hu
  have hu_final : IsStarProjection (u * star u) :=
    isStarProjection_self_mul_star_of_mem_extremePoints_unitClosedBall hu
  have hφ_apply (x : M) : φ x = gM (x * u) := by
    have hx := congrArg (fun f : σ(M, P) →L[ℂ] ℂ ↦ f (toUltraweak ℂ P x)) hφσ
    simpa [φ, gM] using hx
  have hφ_final : φ (u * star u) = φ 1 := by
    rw [hφ_apply, hφ_apply]
    simp only [one_mul]
    rw [hu_initial.mul_star_mul_self]
  have hsupport_le : φ.support hφ ≤ ⟨u * star u, hu_final⟩ :=
    (φ.support_le_iff_apply_eq_apply_one hφ ⟨u * star u, hu_final⟩).2 hφ_final
  let q : M := (φ.support hφ).1
  have hq : IsStarProjection q := (φ.support hφ).2
  have hq_mul_final : q * (u * star u) = q :=
    (hq.le_iff_mul_eq_left hu_final).mp hsupport_le
  have hfinal_mul_q : (u * star u) * q = q :=
    (hq.le_iff_mul_eq_right hu_final).mp hsupport_le
  let v : M := star u * q
  have hvstar : star v = q * u := by
    simp only [v, star_mul, hq.isSelfAdjoint.star_eq, star_star]
  have hv_initial : star v * v = q := by
    rw [hvstar]
    simp only [v]
    calc
      (q * u) * (star u * q) = q * (u * star u) * q := by noncomm_ring
      _ = q := by rw [hq_mul_final, hq.isIdempotentElem.eq]
  have hv_initial_proj : IsStarProjection (star v * v) := hv_initial.symm ▸ hq
  have hgvstar : gM (star v) = (‖gM‖ : ℂ) := by
    calc
      gM (star v) = gM (q * u) := by rw [hvstar]
      _ = φ q := (hφ_apply q).symm
      _ = φ 1 := by simpa only [q, mul_one] using φ.apply_support_mul hφ 1
      _ = (‖φ.toContinuousLinearMap‖ : ℂ) :=
        (PositiveContinuousLinearMap.ofReal_opNorm_eq_map_one
          φ.toPositiveContinuousLinearMap).symm
      _ = (‖gM‖ : ℂ) := by
        change (‖(φσ.comp (toUltraweakPosCLM P)).toContinuousLinearMap‖ : ℂ) =
          (‖g.comp (toUltraweakL ℂ M P)‖ : ℂ)
        exact_mod_cast hnorm.symm
  have hg_cutdown (x : M) : gM (x * (v * star v)) = gM x := by
    have hzero := apply_mul_one_sub_final_eq_zero gM v x hv_initial_proj hgvstar
    rw [mul_sub, mul_one, map_sub, sub_eq_zero] at hzero
    exact hzero.symm
  refine ⟨v, φ, hφ, ?_, ?_, by simpa only [q] using hv_initial⟩
  · ext x
    change gM x = φ (x * v)
    rw [hφ_apply]
    calc
      gM x = gM (x * (v * star v)) := (hg_cutdown x).symm
      _ = gM ((x * v) * star v) := congrArg gM (mul_assoc x v (star v)).symm
      _ = gM ((x * v) * (q * u)) := by rw [hvstar]
      _ = gM ((x * v) * u) := by
        congr 1
        simp only [v, mul_assoc]
        rw [← mul_assoc q q u, hq.isIdempotentElem.eq]
  · change ‖g.comp (toUltraweakL ℂ M P)‖ =
      ‖(φσ.comp (toUltraweakPosCLM P)).toContinuousLinearMap‖
    exact hnorm

private lemma support_le_of_eq_cutoff
    {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] [WStarAlgebra M]
    (φ ψ : M →ₚ[ℂ] ℂ)
    (hφ : φ.IsNormalOnProjections) (hψ : ψ.IsNormalOnProjections)
    (v w : M)
    (hv : star v * v = (φ.support hφ).1)
    (hcut : φ.cutoff v = ψ.cutoff w) :
    φ.support hφ ≤ ψ.support hψ := by
  let q : M := (φ.support hφ).1
  let r : M := (ψ.support hψ).1
  have hq : IsStarProjection q := (φ.support hφ).2
  have hr : IsStarProjection r := (ψ.support hψ).2
  have heval := congrArg
    (fun f : M →L[ℂ] ℂ ↦ f ((1 - r) * star v)) hcut
  have hzero : φ (1 - r) = 0 := by
    calc
      φ (1 - r) = φ ((1 - r) * q) := by
        simpa only [q] using (φ.apply_mul_support hφ (1 - r)).symm
      _ = φ (((1 - r) * star v) * v) := by
        congr 1
        rw [mul_assoc, hv]
      _ = φ.cutoff v ((1 - r) * star v) := by simp
      _ = ψ.cutoff w ((1 - r) * star v) := heval
      _ = ψ (((1 - r) * star v) * w) := by simp
      _ = ψ (r * (((1 - r) * star v) * w)) :=
        (ψ.apply_support_mul hψ (((1 - r) * star v) * w)).symm
      _ = 0 := by
        rw [show r * (((1 - r) * star v) * w) = 0 by
          calc
            r * (((1 - r) * star v) * w) =
                (r * (1 - r)) * star v * w := by noncomm_ring
            _ = 0 := by rw [hr.mul_one_sub_self, zero_mul, zero_mul]]
        exact map_zero ψ
  have hφr : φ r = φ 1 := by
    have hz := hzero
    rw [map_sub, sub_eq_zero] at hz
    exact hz.symm
  exact (φ.support_le_iff_apply_eq_apply_one hφ (ψ.support hψ)).2 hφr

private theorem functional_polar_decomposition_unique
    {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] [WStarAlgebra M]
    (g : M →L[ℂ] ℂ)
    (v w : M) (φ ψ : M →ₚ[ℂ] ℂ)
    (hφ : φ.IsNormalOnProjections) (hψ : ψ.IsNormalOnProjections)
    (hgv : g = φ.cutoff v) (hgw : g = ψ.cutoff w)
    (hgnormφ : ‖g‖ = ‖φ.toContinuousLinearMap‖)
    (hgnormψ : ‖g‖ = ‖ψ.toContinuousLinearMap‖)
    (hv : star v * v = (φ.support hφ).1)
    (hw : star w * w = (ψ.support hψ).1) :
    v = w ∧ φ = ψ := by
  have hcut : φ.cutoff v = ψ.cutoff w := hgv.symm.trans hgw
  have hsupport_le : φ.support hφ ≤ ψ.support hψ :=
    support_le_of_eq_cutoff φ ψ hφ hψ v w hv hcut
  have hsupport_ge : ψ.support hψ ≤ φ.support hφ :=
    support_le_of_eq_cutoff ψ φ hψ hφ w v hw hcut.symm
  have hsupport : φ.support hφ = ψ.support hψ :=
    le_antisymm hsupport_le hsupport_ge
  let q : M := (φ.support hφ).1
  have hq : IsStarProjection q := (φ.support hφ).2
  have hwq : star w * w = q := by
    rw [hw, ← hsupport]
  have hnorm : ‖φ.toContinuousLinearMap‖ = ‖ψ.toContinuousLinearMap‖ := by
    rw [← hgnormφ, ← hgnormψ]
  have hcross : φ (star w * v) = φ 1 := by
    have heval := congrArg (fun f : M →L[ℂ] ℂ ↦ f (star w)) hcut
    calc
      φ (star w * v) = φ.cutoff v (star w) := by simp
      _ = ψ.cutoff w (star w) := heval
      _ = ψ (star w * w) := by simp
      _ = ψ q := by rw [hwq]
      _ = ψ 1 := by
        have hq_eq : q = (ψ.support hψ).1 := by simp only [q, hsupport]
        rw [hq_eq]
        simpa only [one_mul] using ψ.apply_mul_support hψ 1
      _ = (‖ψ.toContinuousLinearMap‖ : ℂ) :=
        (PositiveContinuousLinearMap.ofReal_opNorm_eq_map_one
          ψ.toPositiveContinuousLinearMap).symm
      _ = (‖φ.toContinuousLinearMap‖ : ℂ) := by rw [hnorm]
      _ = φ 1 := PositiveContinuousLinearMap.ofReal_opNorm_eq_map_one
        φ.toPositiveContinuousLinearMap
  have hcross_star : φ (star v * w) = φ 1 := by
    calc
      φ (star v * w) = φ (star (star w * v)) := by rw [star_mul, star_star]
      _ = star (φ (star w * v)) := map_star φ (star w * v)
      _ = star (φ 1) := by rw [hcross]
      _ = φ 1 := by rw [← map_star φ, star_one]
  have hφq : φ q = φ 1 := by
    simpa only [q, one_mul] using φ.apply_mul_support hφ 1
  have hquad : φ (star (v - w) * (v - w)) = 0 := by
    rw [star_sub]
    calc
      φ ((star v - star w) * (v - w)) =
          φ (star v * v) - φ (star v * w) - φ (star w * v) + φ (star w * w) := by
            simp only [sub_mul, mul_sub, map_sub]
            ring
      _ = 0 := by
        rw [hv, hwq, hcross, hcross_star, hφq]
        ring
  have hdiff_q : (v - w) * q = 0 :=
    (φ.apply_star_mul_self_eq_zero_iff_mul_support_eq_zero hφ (v - w)).mp hquad
  have hvqeq : star v * v = q := by simpa only [q] using hv
  have hvq : v * q = v := by
    rw [← hvqeq]
    exact (hvqeq.symm ▸ hq).mul_star_mul_self_assoc
  have hwq' : w * q = w := by
    rw [← hwq]
    exact (hwq.symm ▸ hq).mul_star_mul_self_assoc
  have hvw : v = w := by
    rw [sub_mul, hvq, hwq', sub_eq_zero] at hdiff_q
    exact hdiff_q
  refine ⟨hvw, ?_⟩
  ext x
  calc
    φ x = φ (x * q) := by simpa only [q] using (φ.apply_mul_support hφ x).symm
    _ = φ ((x * star v) * v) := by rw [mul_assoc, hv]
    _ = g (x * star v) := by rw [hgv]; simp
    _ = g (x * star w) := by rw [hvw]
    _ = ψ ((x * star w) * w) := by rw [hgw]; simp
    _ = ψ (x * q) := by rw [mul_assoc, hwq]
    _ = ψ x := by
      simpa only [q, hsupport] using ψ.apply_mul_support hψ x

/-- A normal functional has a unique positive right factor with the norm and initial-support
normalizations.  The source-facing theorem below adds Sakai's final-projection clause. -/
theorem existsUnique_functional_polar_decomposition_basic
    {M P : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
    [WStarAlgebra M]
    [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]
    (g : σ(M, P) →L[ℂ] ℂ) :
    ∃! polar : M × (M →ₚ[ℂ] ℂ),
      ∃ hφ : polar.2.IsNormalOnProjections,
        g.comp (toUltraweakL ℂ M P) = polar.2.cutoff polar.1 ∧
          ‖g.comp (toUltraweakL ℂ M P)‖ =
            ‖polar.2.toContinuousLinearMap‖ ∧
          star polar.1 * polar.1 = (polar.2.support hφ).1 := by
  by_cases hM : Nontrivial M
  · letI := hM
    obtain ⟨v, φ, hφ, hfactor, hnorm, hinitial⟩ :=
      exists_functional_polar_decomposition g
    refine ⟨(v, φ), ⟨hφ, hfactor, hnorm, hinitial⟩, ?_⟩
    rintro ⟨w, ψ⟩ ⟨hψ, hfactor', hnorm', hinitial'⟩
    obtain ⟨hvw, hφψ⟩ := functional_polar_decomposition_unique
      (g.comp (toUltraweakL ℂ M P)) v w φ ψ hφ hψ
      hfactor hfactor' hnorm hnorm' hinitial hinitial'
    exact Prod.ext hvw.symm hφψ.symm
  · letI : Subsingleton M := not_nontrivial_iff_subsingleton.mp hM
    let φσ : σ(M, P) →P[ℂ] ℂ := 0
    let φ : M →ₚ[ℂ] ℂ :=
      (φσ.comp (toUltraweakPosCLM P)).toPositiveLinearMap
    have hφ : φ.IsNormalOnProjections :=
      PositiveContinuousLinearMap.comp_toUltraweakPosCLM_isNormalOnProjections φσ
    have hfactor : g.comp (toUltraweakL ℂ M P) = φ.cutoff 0 := by
      ext x
      have hx : x = 0 := Subsingleton.elim x 0
      simp [hx]
    have hnorm : ‖g.comp (toUltraweakL ℂ M P)‖ =
        ‖φ.toContinuousLinearMap‖ := by
      rw [hfactor]
      simp
    have hinitial : star (0 : M) * 0 = (φ.support hφ).1 :=
      Subsingleton.elim _ _
    refine ⟨(0, φ), ⟨hφ, hfactor, hnorm, hinitial⟩, ?_⟩
    rintro ⟨w, ψ⟩ -
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · ext x
      have hx : x = 0 := Subsingleton.elim x 0
      simp [hx]

/-- The absolute value, i.e. the canonical positive factor, of a normal functional. -/
noncomputable def functionalAbs
    {M P : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
    [WStarAlgebra M]
    [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]
    (g : σ(M, P) →L[ℂ] ℂ) : M →ₚ[ℂ] ℂ :=
  (existsUnique_functional_polar_decomposition_basic g).choose.2

/-- The absolute value of a normal functional is normal on projections. -/
theorem functionalAbs_isNormalOnProjections
    {M P : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
    [WStarAlgebra M]
    [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]
    (g : σ(M, P) →L[ℂ] ℂ) :
    (functionalAbs g).IsNormalOnProjections := by
  exact (existsUnique_functional_polar_decomposition_basic g).choose_spec.1.choose

/-- The canonical functional absolute value occurs in a normalized polar decomposition. -/
theorem functionalAbs_spec
    {M P : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
    [WStarAlgebra M]
    [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]
    (g : σ(M, P) →L[ℂ] ℂ) :
    ∃ v : M,
      g.comp (toUltraweakL ℂ M P) = (functionalAbs g).cutoff v ∧
        ‖g.comp (toUltraweakL ℂ M P)‖ =
          ‖(functionalAbs g).toContinuousLinearMap‖ ∧
        star v * v =
          ((functionalAbs g).support (functionalAbs_isNormalOnProjections g)).1 := by
  let h := existsUnique_functional_polar_decomposition_basic g
  refine ⟨h.choose.1, ?_⟩
  obtain ⟨hφ, hfactor, hnorm, hinitial⟩ := h.choose_spec.1
  simpa only [functionalAbs, Subtype.coe_eta] using
    And.intro hfactor (And.intro hnorm hinitial)

/-- Taking the functional absolute value preserves the operator norm. -/
theorem norm_functionalAbs
    {M P : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
    [WStarAlgebra M]
    [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]
    (g : σ(M, P) →L[ℂ] ℂ) :
    ‖(functionalAbs g).toContinuousLinearMap‖ =
      ‖g.comp (toUltraweakL ℂ M P)‖ := by
  obtain ⟨_, _, hnorm, _⟩ := functionalAbs_spec g
  exact hnorm.symm

/-- Any positive factor satisfying Sakai's normalized support condition is the canonical
absolute value of the normal functional. -/
theorem eq_functionalAbs_of_polar_decomposition
    {M P : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
    [WStarAlgebra M]
    [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]
    (g : σ(M, P) →L[ℂ] ℂ) (v : M) (φ : M →ₚ[ℂ] ℂ)
    (hφ : φ.IsNormalOnProjections)
    (hfactor : g.comp (toUltraweakL ℂ M P) = φ.cutoff v)
    (hnorm : ‖g.comp (toUltraweakL ℂ M P)‖ = ‖φ.toContinuousLinearMap‖)
    (hinitial : star v * v = (φ.support hφ).1) :
    φ = functionalAbs g := by
  let h := existsUnique_functional_polar_decomposition_basic g
  have hpairs : (v, φ) = h.choose :=
    h.choose_spec.2 (v, φ) ⟨hφ, hfactor, hnorm, hinitial⟩
  exact congrArg Prod.snd hpairs

private lemma support_eq_of_eq
    {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
    [WStarAlgebra M] {φ ψ : M →ₚ[ℂ] ℂ}
    (h : φ = ψ) (hφ : φ.IsNormalOnProjections) (hψ : ψ.IsNormalOnProjections) :
    (φ.support hφ).1 = (ψ.support hψ).1 := by
  subst ψ
  rfl

/-- The final projection in a functional polar decomposition is the support of the absolute
value of the adjoint functional. -/
theorem functional_polar_decomposition_final_projection
    {M P : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
    [WStarAlgebra M]
    [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]
    (g : σ(M, P) →L[ℂ] ℂ) (v : M) (φ : M →ₚ[ℂ] ℂ)
    (hφ : φ.IsNormalOnProjections)
    (hfactor : g.comp (toUltraweakL ℂ M P) = φ.cutoff v)
    (hnorm : ‖g.comp (toUltraweakL ℂ M P)‖ = ‖φ.toContinuousLinearMap‖)
    (hinitial : star v * v = (φ.support hφ).1) :
    v * star v =
      ((functionalAbs (star (WithConv.toConv g)).ofConv).support
        (functionalAbs_isNormalOnProjections
          (star (WithConv.toConv g)).ofConv)).1 := by
  let gM : M →L[ℂ] ℂ := g.comp (toUltraweakL ℂ M P)
  let gStar : σ(M, P) →L[ℂ] ℂ := (star (WithConv.toConv g)).ofConv
  let gStarM : M →L[ℂ] ℂ := gStar.comp (toUltraweakL ℂ M P)
  let ψ : M →ₚ[ℂ] ℂ := φ.conjugate v
  let hψ : ψ.IsNormalOnProjections := hφ.conjugate (P := P) v
  have hgStar_apply (x : M) : gStarM x = star (gM (star x)) := by
    simp only [gStarM, gStar, gM, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.intrinsicStar_apply, toUltraweakL_apply]
    rw [← toUltraweak_star]
  have hfactorStar : gStarM = ψ.cutoff (star v) := by
    ext x
    have hx := congrArg (fun f : M →L[ℂ] ℂ ↦ f (star x)) hfactor
    calc
      gStarM x = star (gM (star x)) := hgStar_apply x
      _ = star (φ (star x * v)) := by
        simpa only [PositiveLinearMap.cutoff_apply] using congrArg star hx
      _ = φ (star (star x * v)) := (map_star φ (star x * v)).symm
      _ = φ (star v * x) := by rw [star_mul, star_star]
      _ = φ ((star v * x) * (φ.support hφ).1) :=
        (φ.apply_mul_support hφ (star v * x)).symm
      _ = φ ((star v * x) * (star v * v)) := by rw [hinitial]
      _ = ψ (x * star v) := by
        simp only [ψ, PositiveLinearMap.conjugate_apply]
        congr 1
        noncomm_ring
      _ = ψ.cutoff (star v) x := rfl
  have hnormStar : ‖gStarM‖ = ‖gM‖ := by
    apply le_antisymm
    · refine gStarM.opNorm_le_bound (norm_nonneg _) fun x ↦ ?_
      rw [hgStar_apply, norm_star]
      calc
        ‖gM (star x)‖ ≤ ‖gM‖ * ‖star x‖ := gM.le_opNorm _
        _ = ‖gM‖ * ‖x‖ := by rw [norm_star]
    · refine gM.opNorm_le_bound (norm_nonneg _) fun x ↦ ?_
      calc
        ‖gM x‖ = ‖gStarM (star x)‖ := by rw [hgStar_apply, star_star, norm_star]
        _ ≤ ‖gStarM‖ * ‖star x‖ := gStarM.le_opNorm _
        _ = ‖gStarM‖ * ‖x‖ := by rw [norm_star]
  have hψnorm : ‖ψ.toContinuousLinearMap‖ = ‖φ.toContinuousLinearMap‖ := by
    exact_mod_cast calc
      (‖ψ.toContinuousLinearMap‖ : ℂ) = ψ 1 :=
        PositiveContinuousLinearMap.ofReal_opNorm_eq_map_one
          ψ.toPositiveContinuousLinearMap
      _ = φ (star v * v) := by simp only [ψ, PositiveLinearMap.conjugate_apply, mul_one]
      _ = φ (φ.support hφ).1 := by rw [hinitial]
      _ = φ 1 := by
        simpa only [one_mul] using φ.apply_mul_support hφ 1
      _ = (‖φ.toContinuousLinearMap‖ : ℂ) :=
        (PositiveContinuousLinearMap.ofReal_opNorm_eq_map_one
          φ.toPositiveContinuousLinearMap).symm
  have hnormStarψ : ‖gStarM‖ = ‖ψ.toContinuousLinearMap‖ := by
    calc
      ‖gStarM‖ = ‖gM‖ := hnormStar
      _ = ‖φ.toContinuousLinearMap‖ := hnorm
      _ = ‖ψ.toContinuousLinearMap‖ := hψnorm.symm
  have hinitialStar : star (star v) * star v = (ψ.support hψ).1 := by
    simpa only [star_star, ψ, hψ] using
      (PositiveLinearMap.support_conjugate_eq_mul_star
        φ hφ v hinitial).symm
  have hψabs : ψ = functionalAbs gStar :=
    eq_functionalAbs_of_polar_decomposition gStar (star v) ψ hψ
      hfactorStar hnormStarψ hinitialStar
  calc
    v * star v = (ψ.support hψ).1 := by
      simpa only [ψ, hψ] using
        (PositiveLinearMap.support_conjugate_eq_mul_star
          φ hφ v hinitial).symm
    _ = ((functionalAbs gStar).support
        (functionalAbs_isNormalOnProjections gStar)).1 :=
      support_eq_of_eq hψabs hψ (functionalAbs_isNormalOnProjections gStar)

/-- **Sakai, Theorem 1.14.4.** Every normal functional has a unique polar decomposition
`g x = φ (x * v)`.  The positive factor is normal and has the same norm as `g`; the initial
projection `v⋆ * v` is its support, and the final projection `v * v⋆` is the support of the
absolute value of the adjoint functional. -/
theorem existsUnique_functional_polar_decomposition
    {M P : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
    [WStarAlgebra M]
    [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]
    (g : σ(M, P) →L[ℂ] ℂ) :
    ∃! polar : M × (M →ₚ[ℂ] ℂ),
      ∃ hφ : polar.2.IsNormalOnProjections,
        g.comp (toUltraweakL ℂ M P) = polar.2.cutoff polar.1 ∧
          ‖g.comp (toUltraweakL ℂ M P)‖ =
            ‖polar.2.toContinuousLinearMap‖ ∧
          star polar.1 * polar.1 = (polar.2.support hφ).1 ∧
          polar.1 * star polar.1 =
            ((functionalAbs (star (WithConv.toConv g)).ofConv).support
              (functionalAbs_isNormalOnProjections
                (star (WithConv.toConv g)).ofConv)).1 := by
  let h := existsUnique_functional_polar_decomposition_basic g
  refine ⟨h.choose, ?_, ?_⟩
  · obtain ⟨hφ, hfactor, hnorm, hinitial⟩ := h.choose_spec.1
    exact ⟨hφ, hfactor, hnorm, hinitial,
      functional_polar_decomposition_final_projection g h.choose.1 h.choose.2
        hφ hfactor hnorm hinitial⟩
  · intro polar hpolar
    apply h.choose_spec.2 polar
    obtain ⟨hφ, hfactor, hnorm, hinitial, _⟩ := hpolar
    exact ⟨hφ, hfactor, hnorm, hinitial⟩

end

end Ultraweak
