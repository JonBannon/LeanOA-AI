module

public import LeanOA.Ultraweak.Multiplication
public import Mathlib.Topology.Algebra.Star.LinearMap

import LeanOA.CStarAlgebra.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.LocallyConvex.WeakDual

@[expose] public section

/-!
# Polar decomposition of ultraweakly continuous functionals

This file proves the polar decomposition needed to compare the strong and ultraweak topologies.
A self-adjoint ultraweakly continuous functional is a positive ultraweakly continuous functional
precomposed with left multiplication by a self-adjoint unitary.
-/

open Metric Set
open scoped ComplexOrder ComplexStarModule Ultraweak

namespace Ultraweak

noncomputable section

private lemma exists_selfAdjoint_norm_le_norm_apply_re_eq_norm_apply
    {A : Type*} [CStarAlgebra A] (f : A →L[ℂ] ℂ)
    (hf : ∀ x, f (star x) = star (f x)) (x : A) :
    ∃ a : A, IsSelfAdjoint a ∧ ‖a‖ ≤ ‖x‖ ∧ (f a).re = ‖f x‖ := by
  by_cases hx : f x = 0
  · exact ⟨0, by simp, by simp, by simp [hx]⟩
  let c : ℂ := star (f x) / ‖f x‖
  let a : A := ℜ (c • x)
  refine ⟨a, (ℜ (c • x)).2, ?_, ?_⟩
  · calc
      ‖a‖ ≤ ‖c • x‖ := by
        change ‖(ℜ (c • x) : selfAdjoint A)‖ ≤ ‖c • x‖
        exact realPart.norm_le (c • x)
      _ = ‖x‖ := by
        rw [norm_smul, show c = star (f x) / ‖f x‖ by rfl, norm_div, norm_star,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
          div_self (norm_ne_zero_iff.mpr hx), one_mul]
  rw [show f a = ℜ (f (c • x)) by
    simp only [a, realPart_apply_coe, map_smul, map_add, hf, star_smul, RCLike.star_def,
      ← Complex.coe_smul]]
  have hphase : star (f x) / ‖f x‖ * f x = (‖f x‖ : ℂ) := by
    rw [RCLike.star_def, div_mul_eq_mul_div, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq]
    push_cast
    field_simp [norm_ne_zero_iff.mpr hx]
  rw [show c = star (f x) / ‖f x‖ by rfl, map_smul, smul_eq_mul, hphase]
  simp

private theorem exists_positive_comp_mulLeft_of_isSelfAdjoint_of_nontrivial
    {M P : Type*} [CStarAlgebra M] [Nontrivial M] [PartialOrder M] [StarOrderedRing M]
    [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]
    (f : σ(M, P) →L[ℂ] ℂ) (hf : IsSelfAdjoint (WithConv.toConv f)) :
    ∃ (u : M) (phi : σ(M, P) →P[ℂ] ℂ), IsSelfAdjoint u ∧ u ∈ unitary M ∧
      f = phi.toContinuousLinearMap.comp (mulLeftL (P := P) u) := by
  letI : ContinuousSMul ℝ σ(M, P) := ⟨by
    have hsmul : Continuous fun p : ℂ × σ(M, P) ↦ p.1 • p.2 := continuous_smul
    convert hsmul.comp
      ((Complex.continuous_ofReal.comp continuous_fst).prodMk continuous_snd) using 1
    ext x
    exact RCLike.real_smul_eq_coe_smul (K := ℂ) x.1 x.2⟩
  letI : LocallyConvexSpace ℂ σ(M, P) := Ultraweak.locallyConvexSpace ℂ M P
  letI : LocallyConvexSpace ℝ σ(M, P) :=
    LocallyConvexSpace.to_real ℂ σ(M, P) inferInstance
  let f' : M →L[ℂ] ℂ := f.comp (toUltraweakPosCLM P).toContinuousLinearMap
  have hf' (x : M) : f' (star x) = star (f' x) := by
    simpa [f'] using
      (ContinuousLinearMap.IntrinsicStar.isSelfAdjoint_iff_map_star (WithConv.toConv f)).mp hf
        (toUltraweak ℂ P x)
  let S : Set σ(M, P) :=
    ofUltraweak ⁻¹' closedBall (0 : M) 1 ∩ {x | IsSelfAdjoint x}
  have hS : IsCompact S := by
    exact (isCompact_closedBall ℂ P (0 : M) 1).inter_right isClosed_setOf_isSelfAdjoint
  let fr : σ(M, P) →L[ℝ] ℝ := RCLike.reCLM.comp (f.restrictScalars ℝ)
  let K := fr.toExposed S
  obtain ⟨z, hzS, hz⟩ := hS.exists_isMaxOn
    (show S.Nonempty from ⟨0, by simp [S]⟩) fr.continuous.continuousOn
  have hK : IsCompact K := ContinuousLinearMap.toExposed.isExposed.isCompact hS
  obtain ⟨uσ, huK⟩ := hK.extremePoints_nonempty ⟨z, hzS, hz⟩
  have huS : uσ ∈ extremePoints ℝ S :=
    ContinuousLinearMap.toExposed.isExposed.isExtreme.extremePoints_subset_extremePoints huK
  let e := (linearEquiv ℂ M P).restrictScalars ℝ
  have heS : e '' S = {x : M | IsSelfAdjoint x ∧ x ∈ closedBall 0 1} := by
    ext x
    simp only [mem_image, mem_inter_iff, mem_preimage, mem_setOf_eq, S]
    constructor
    · rintro ⟨y, ⟨hyb, hysa⟩, rfl⟩
      exact ⟨by simpa [e] using hysa, by simpa [e] using hyb⟩
    · rintro ⟨hxsa, hxb⟩
      refine ⟨toUltraweak ℂ P x, ⟨?_, ?_⟩, by simp [e]⟩
      · simpa using hxb
      · simpa using hxsa
  have huM : IsSelfAdjoint (ofUltraweak uσ) ∧ ofUltraweak uσ ∈ unitary M := by
    rw [← mem_extremePoints_isSelfAdjoint_and_mem_unitClosedBall_iff_isSelfAdjoint_and_mem_unitary,
      ← heS, ← image_extremePoints]
    exact ⟨uσ, huS, by simp [e]⟩
  let u := ofUltraweak uσ
  have huMax : ∀ y ∈ S, fr y ≤ fr uσ := huK.1.2
  have hunit (x : M) (hx : ‖x‖ ≤ 1) : ‖f' x‖ ≤ (f' u).re := by
    obtain ⟨a, ha, han, haf⟩ :=
      exists_selfAdjoint_norm_le_norm_apply_re_eq_norm_apply f' hf' x
    rw [← haf]
    exact huMax (toUltraweak ℂ P a) <| by
      refine ⟨?_, by simpa using ha⟩
      simpa [mem_closedBall_zero_iff] using han.trans hx
  have hB : 0 ≤ (f' u).re := by simpa using hunit 0 (by simp)
  have hf'norm_le : ‖f'‖ ≤ (f' u).re :=
    f'.opNorm_le_of_unit_norm hB fun x hx ↦ hunit x hx.le
  have hfu_real : ((f' u).re : ℂ) = f' u := by
    have h : f' u = star (f' u) := by simpa [u, huM.1.star_eq] using hf' u
    exact Complex.conj_eq_iff_re.mp h.symm
  have hf'norm_ge : (f' u).re ≤ ‖f'‖ := by
    calc
      (f' u).re = ‖f' u‖ := by
        rw [← hfu_real, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hB,
          Complex.ofReal_re]
      _ ≤ ‖f'‖ * ‖u‖ := f'.le_opNorm u
      _ = ‖f'‖ := by rw [CStarRing.norm_of_mem_unitary huM.2, mul_one]
  have hf'norm : (‖f'‖ : ℂ) = f' u := by
    rw [← hfu_real]
    exact_mod_cast le_antisymm hf'norm_le hf'norm_ge
  let g : σ(M, P) →L[ℂ] ℂ := f.comp (mulLeftL (P := P) u)
  let g' : M →L[ℂ] ℂ := g.comp (toUltraweakPosCLM P).toContinuousLinearMap
  let U : unitary M := ⟨u, huM.2⟩
  have hg'norm_le : ‖g'‖ ≤ ‖f'‖ := by
    refine g'.opNorm_le_bound (norm_nonneg f') fun x ↦ ?_
    calc
      ‖g' x‖ = ‖f' (u * x)‖ := rfl
      _ ≤ ‖f'‖ * ‖u * x‖ := f'.le_opNorm _
      _ = ‖f'‖ * ‖x‖ := by
        rw [show u = (U : M) by rfl, CStarRing.norm_coe_unitary_mul]
  have hg'one : g' 1 = f' u := by simp [g', g, f', u]
  have hg'norm_ge : ‖f'‖ ≤ ‖g'‖ := by
    calc
      ‖f'‖ = ‖g' 1‖ := by
        rw [hg'one, ← hf'norm, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (norm_nonneg _)]
      _ ≤ ‖g'‖ * ‖(1 : M)‖ := g'.le_opNorm 1
      _ = ‖g'‖ := by simp
  have hg'norm : (‖g'‖ : ℂ) = g' 1 := by
    rw [hg'one, ← hf'norm]
    exact_mod_cast le_antisymm hg'norm_le hg'norm_ge
  have hg'mono : Monotone g' :=
    ContinuousLinearMap.monotone_iff_opNorm_eq_map_one.mpr hg'norm
  let phi : σ(M, P) →P[ℂ] ℂ := PositiveContinuousLinearMap.mk₀ g fun x hx ↦ by
    change 0 ≤ g' (ofUltraweak x)
    exact (monotone_iff_map_nonneg g').mp hg'mono _ <| ofUltraweak_nonneg.mpr hx
  refine ⟨u, phi, huM.1, huM.2, ?_⟩
  ext x
  change f x = g (mulLeftL (P := P) u x)
  have huSelf : IsSelfAdjoint u := by simpa [u] using huM.1
  have huu : u * u = 1 := by
    calc
      u * u = star u * u := congrArg (· * u) huSelf.star_eq.symm
      _ = 1 := (Unitary.mem_iff.mp huM.2).1
  change f x = f (toUltraweak ℂ P u * (toUltraweak ℂ P u * x))
  congr 1
  rw [← ofUltraweak_inj]
  simp only [ofUltraweak_mul, ofUltraweak_toUltraweak]
  rw [← mul_assoc, huu, one_mul]

/-- A self-adjoint ultraweakly continuous functional is a positive ultraweakly continuous
functional precomposed with left multiplication by a self-adjoint unitary. -/
theorem exists_positive_comp_mulLeft_of_isSelfAdjoint
    {M P : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
    [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]
    (f : σ(M, P) →L[ℂ] ℂ) (hf : IsSelfAdjoint (WithConv.toConv f)) :
    ∃ (u : M) (phi : σ(M, P) →P[ℂ] ℂ), IsSelfAdjoint u ∧ u ∈ unitary M ∧
      f = phi.toContinuousLinearMap.comp (mulLeftL (P := P) u) := by
  by_cases hM : Nontrivial M
  · letI := hM
    exact exists_positive_comp_mulLeft_of_isSelfAdjoint_of_nontrivial f hf
  · letI : Subsingleton M := not_nontrivial_iff_subsingleton.mp hM
    refine ⟨0, 0, by simp, ?_, ?_⟩
    · have h01 : (0 : M) = 1 := Subsingleton.elim _ _
      rw [h01]
      exact one_mem (unitary M)
    · ext x
      have hx : x = 0 := Subsingleton.elim x 0
      simp [hx]

end

end Ultraweak
