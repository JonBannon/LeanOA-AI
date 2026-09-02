module

public import LeanOA.Ultraweak.FunctionalSupport
public import LeanOA.Ultraweak.PolarDecomposition

@[expose] public section

/-!
# Orthogonal decomposition of self-adjoint normal functionals

This file formalizes Sakai's norm orthogonality for normal positive functionals and the unique
orthogonal decomposition of a self-adjoint normal functional. The existence proof splits the
self-adjoint unitary supplied by the existing functional polar-factorization theorem into two
complementary projections. Functional support is used for uniqueness and for the structural
characterization of orthogonality.
-/

open scoped ComplexOrder ComplexStarModule Ultraweak

namespace Ultraweak

noncomputable section

private lemma isStarProjection_half_one_add_of_isSelfAdjoint_mul_self_eq_one
    {A : Type*} [CStarAlgebra A] {u : A} (hu : IsSelfAdjoint u)
    (huu : u * u = 1) :
    IsStarProjection ((2 : ℂ)⁻¹ • (1 + u)) := by
  rw [isStarProjection_iff']
  constructor
  · rw [smul_mul_smul]
    simp only [mul_add, add_mul, one_mul, mul_one, huu]
    module
  · rw [star_smul, star_add, star_one, hu.star_eq]
    norm_num

private lemma positive_factor_centralizes_selfAdjoint_unitary
    {M P : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
    [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]
    (f : σ(M, P) →L[ℂ] ℂ) (hf : IsSelfAdjoint (WithConv.toConv f))
    (u : M) (hu : IsSelfAdjoint u) (φ : σ(M, P) →P[ℂ] ℂ)
    (hfac : f = φ.toContinuousLinearMap.comp (mulLeftL (P := P) u))
    (x : M) :
    φ (toUltraweak ℂ P (u * x)) = φ (toUltraweak ℂ P (x * u)) := by
  have hfstar (y : σ(M, P)) : f (star y) = star (f y) :=
    (ContinuousLinearMap.IntrinsicStar.isSelfAdjoint_iff_map_star
      (WithConv.toConv f)).mp hf y
  calc
    φ (toUltraweak ℂ P (u * x)) = f (toUltraweak ℂ P x) := by
      rw [hfac]
      simp
    _ = star (f (star (toUltraweak ℂ P x))) := by
      simpa using hfstar (star (toUltraweak ℂ P x))
    _ = star (φ (toUltraweak ℂ P (u * star x))) := by
      rw [hfac]
      simp
    _ = φ (star (toUltraweak ℂ P (u * star x))) := by rw [map_star]
    _ = φ (toUltraweak ℂ P (x * u)) := by
      rw [← toUltraweak_star, star_mul, star_star, hu.star_eq]

private theorem split_positive_factor
    {M P : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
    [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]
    (f : σ(M, P) →L[ℂ] ℂ) (hf : IsSelfAdjoint (WithConv.toConv f))
    (u : M) (hu : IsSelfAdjoint u) (huU : u ∈ unitary M)
    (φ : σ(M, P) →P[ℂ] ℂ)
    (hfac : f = φ.toContinuousLinearMap.comp (mulLeftL (P := P) u)) :
    ∃ (p : {p : M // IsStarProjection p}) (φ₁ φ₂ : σ(M, P) →P[ℂ] ℂ),
      f = φ₁.toContinuousLinearMap - φ₂.toContinuousLinearMap ∧
        ‖f.comp (toUltraweakL ℂ M P)‖ =
          ‖(φ₁.comp (toUltraweakPosCLM P)).toContinuousLinearMap‖ +
            ‖(φ₂.comp (toUltraweakPosCLM P)).toContinuousLinearMap‖ ∧
        (φ₁.comp (toUltraweakPosCLM P)) p.1 =
          (φ₁.comp (toUltraweakPosCLM P)) 1 ∧
        (φ₂.comp (toUltraweakPosCLM P)) (1 - p.1) =
          (φ₂.comp (toUltraweakPosCLM P)) 1 := by
  have huu : u * u = 1 := by
    calc
      u * u = star u * u := congrArg (· * u) hu.star_eq.symm
      _ = 1 := (Unitary.mem_iff.mp huU).1
  let p : M := (2 : ℂ)⁻¹ • (1 + u)
  have hp : IsStarProjection p :=
    isStarProjection_half_one_add_of_isSelfAdjoint_mul_self_eq_one hu huu
  let q : M := 1 - p
  have hq : IsStarProjection q := hp.one_sub
  have hu_decomp : u = p - q := by
    simp only [q, p]
    module
  have hpcentral (x : M) :
      φ (toUltraweak ℂ P (p * x)) = φ (toUltraweak ℂ P (x * p)) := by
    simp only [p, smul_mul_assoc, mul_smul_comm, add_mul, mul_add, one_mul, mul_one,
      toUltraweak_smul, toUltraweak_add, map_smul, map_add]
    rw [positive_factor_centralizes_selfAdjoint_unitary f hf u hu φ hfac x]
  have hqcentral (x : M) :
      φ (toUltraweak ℂ P (q * x)) = φ (toUltraweak ℂ P (x * q)) := by
    simp only [q, sub_mul, mul_sub, one_mul, mul_one, toUltraweak_sub, map_sub, hpcentral]
  let φ₁ : σ(M, P) →P[ℂ] ℂ :=
    φ.comp (IsStarProjection.Corner.ultraweakCutdownP (P := P) hp)
  let φ₂ : σ(M, P) →P[ℂ] ℂ :=
    φ.comp (IsStarProjection.Corner.ultraweakCutdownP (P := P) hq)
  have hφ₁ (x : σ(M, P)) :
      φ₁ x = φ (toUltraweak ℂ P (p * ofUltraweak x)) := by
    change φ (toUltraweak ℂ P (p * ofUltraweak x * p)) =
      φ (toUltraweak ℂ P (p * ofUltraweak x))
    calc
      φ (toUltraweak ℂ P (p * ofUltraweak x * p)) =
          φ (toUltraweak ℂ P (p * (ofUltraweak x * p))) := by rw [mul_assoc]
      _ = φ (toUltraweak ℂ P ((ofUltraweak x * p) * p)) := hpcentral _
      _ = φ (toUltraweak ℂ P (ofUltraweak x * p)) := by
        rw [mul_assoc, hp.isIdempotentElem.eq]
      _ = φ (toUltraweak ℂ P (p * ofUltraweak x)) := (hpcentral _).symm
  have hφ₂ (x : σ(M, P)) :
      φ₂ x = φ (toUltraweak ℂ P (q * ofUltraweak x)) := by
    change φ (toUltraweak ℂ P (q * ofUltraweak x * q)) =
      φ (toUltraweak ℂ P (q * ofUltraweak x))
    calc
      φ (toUltraweak ℂ P (q * ofUltraweak x * q)) =
          φ (toUltraweak ℂ P (q * (ofUltraweak x * q))) := by rw [mul_assoc]
      _ = φ (toUltraweak ℂ P ((ofUltraweak x * q) * q)) := hqcentral _
      _ = φ (toUltraweak ℂ P (ofUltraweak x * q)) := by
        rw [mul_assoc, hq.isIdempotentElem.eq]
      _ = φ (toUltraweak ℂ P (q * ofUltraweak x)) := (hqcentral _).symm
  refine ⟨⟨p, hp⟩, φ₁, φ₂, ?_, ?_, ?_, ?_⟩
  · ext x
    rw [hfac]
    simp only [ContinuousLinearMap.comp_apply, mulLeftL_apply, sub_apply,
      PositiveContinuousLinearMap.coe_toContinuousLinearMap]
    rw [hφ₁, hφ₂, hu_decomp, sub_mul, toUltraweak_sub, map_sub]
  · let U : unitary M := ⟨u, huU⟩
    let fM : M →L[ℂ] ℂ := f.comp (toUltraweakL ℂ M P)
    let φM : M →P[ℂ] ℂ := φ.comp (toUltraweakPosCLM P)
    let φ₁M : M →P[ℂ] ℂ := φ₁.comp (toUltraweakPosCLM P)
    let φ₂M : M →P[ℂ] ℂ := φ₂.comp (toUltraweakPosCLM P)
    have hfM_apply (x : M) : fM x = φM (u * x) := by
      simp only [fM, φM, ContinuousLinearMap.comp_apply, toUltraweakL_apply,
        PositiveContinuousLinearMap.comp_apply]
      rw [hfac]
      simp
    have hφM_apply (x : M) : φM x = fM (u * x) := by
      rw [hfM_apply]
      simp only [φM, PositiveContinuousLinearMap.comp_apply]
      rw [← mul_assoc, huu, one_mul]
    have hnorm_f_le : ‖fM‖ ≤ ‖φM.toContinuousLinearMap‖ := by
      apply fM.opNorm_le_bound (norm_nonneg _)
      intro x
      rw [hfM_apply]
      calc
        ‖φM (u * x)‖ ≤ ‖φM.toContinuousLinearMap‖ * ‖u * x‖ :=
          φM.toContinuousLinearMap.le_opNorm _
        _ = ‖φM.toContinuousLinearMap‖ * ‖x‖ := by
          simpa only [show u = (U : M) by rfl] using
            congrArg (‖φM.toContinuousLinearMap‖ * ·) (CStarRing.norm_coe_unitary_mul U x)
    have hnorm_φ_le : ‖φM.toContinuousLinearMap‖ ≤ ‖fM‖ := by
      apply φM.toContinuousLinearMap.opNorm_le_bound (norm_nonneg _)
      intro x
      change ‖φM x‖ ≤ ‖fM‖ * ‖x‖
      rw [hφM_apply]
      calc
        ‖fM (u * x)‖ ≤ ‖fM‖ * ‖u * x‖ := fM.le_opNorm _
        _ = ‖fM‖ * ‖x‖ := by
          simpa only [show u = (U : M) by rfl] using
            congrArg (‖fM‖ * ·) (CStarRing.norm_coe_unitary_mul U x)
    have hnorm_f : ‖fM‖ = ‖φM.toContinuousLinearMap‖ :=
      le_antisymm hnorm_f_le hnorm_φ_le
    have hsum : φ₁ 1 + φ₂ 1 = φ 1 := by
      rw [hφ₁, hφ₂]
      simp only [ofUltraweak_one, mul_one]
      calc
        φ (toUltraweak ℂ P p) + φ (toUltraweak ℂ P q) =
            φ (toUltraweak ℂ P p + toUltraweak ℂ P q) := (map_add φ _ _).symm
        _ = φ (toUltraweak ℂ P (p + q)) := rfl
        _ = φ 1 := by simp [q]
    have hsumM : φ₁M 1 + φ₂M 1 = φM 1 := by
      simpa [φ₁M, φ₂M, φM] using hsum
    have hnorm_φ : (‖φM.toContinuousLinearMap‖ : ℂ) = φM 1 :=
      PositiveContinuousLinearMap.ofReal_opNorm_eq_map_one φM
    have hnorm_φ₁ : (‖φ₁M.toContinuousLinearMap‖ : ℂ) = φ₁M 1 :=
      PositiveContinuousLinearMap.ofReal_opNorm_eq_map_one φ₁M
    have hnorm_φ₂ : (‖φ₂M.toContinuousLinearMap‖ : ℂ) = φ₂M 1 :=
      PositiveContinuousLinearMap.ofReal_opNorm_eq_map_one φ₂M
    rw [hnorm_f]
    exact_mod_cast (calc
      (‖φM.toContinuousLinearMap‖ : ℂ) = φM 1 := hnorm_φ
      _ = φ₁M 1 + φ₂M 1 := hsumM.symm
      _ = (‖φ₁M.toContinuousLinearMap‖ : ℂ) +
          (‖φ₂M.toContinuousLinearMap‖ : ℂ) := by rw [hnorm_φ₁, hnorm_φ₂])
  · change φ₁ (toUltraweak ℂ P p) = φ₁ (toUltraweak ℂ P 1)
    rw [hφ₁, hφ₁]
    simp only [ofUltraweak_toUltraweak, mul_one, hp.isIdempotentElem.eq]
  · change φ₂ (toUltraweak ℂ P (1 - p)) = φ₂ (toUltraweak ℂ P 1)
    rw [hφ₂, hφ₂]
    simp only [ofUltraweak_toUltraweak, mul_one]
    exact congrArg (φ ∘ toUltraweak ℂ P) hq.isIdempotentElem.eq

private theorem exists_orthogonal_decomposition_with_carrier
    {M P : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
    [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]
    (f : σ(M, P) →L[ℂ] ℂ) (hf : IsSelfAdjoint (WithConv.toConv f)) :
    ∃ (p : {p : M // IsStarProjection p}) (f₁ f₂ : M →ₚ[ℂ] ℂ),
      f₁.IsNormalOnProjections ∧ f₂.IsNormalOnProjections ∧
        f.comp (toUltraweakL ℂ M P) =
          f₁.toContinuousLinearMap - f₂.toContinuousLinearMap ∧
        ‖f.comp (toUltraweakL ℂ M P)‖ =
          ‖f₁.toContinuousLinearMap‖ + ‖f₂.toContinuousLinearMap‖ ∧
        f₁ p.1 = f₁ 1 ∧ f₂ (1 - p.1) = f₂ 1 := by
  obtain ⟨u, φ, hu, huU, hfac⟩ := exists_positive_comp_mulLeft_of_isSelfAdjoint f hf
  obtain ⟨p, φ₁, φ₂, hdecomp, hnorm, hcarrier₁, hcarrier₂⟩ :=
    split_positive_factor f hf u hu huU φ hfac
  let f₁ : M →ₚ[ℂ] ℂ := (φ₁.comp (toUltraweakPosCLM P)).toPositiveLinearMap
  let f₂ : M →ₚ[ℂ] ℂ := (φ₂.comp (toUltraweakPosCLM P)).toPositiveLinearMap
  refine ⟨p, f₁, f₂,
    PositiveContinuousLinearMap.comp_toUltraweakPosCLM_isNormalOnProjections φ₁,
    PositiveContinuousLinearMap.comp_toUltraweakPosCLM_isNormalOnProjections φ₂,
    ?_, ?_, hcarrier₁, hcarrier₂⟩
  · ext x
    have hx := congrArg (fun g : σ(M, P) →L[ℂ] ℂ ↦ g (toUltraweak ℂ P x)) hdecomp
    simpa [f₁, f₂] using hx
  · change ‖f.comp (toUltraweakL ℂ M P)‖ =
      ‖(φ₁.comp (toUltraweakPosCLM P)).toContinuousLinearMap‖ +
        ‖(φ₂.comp (toUltraweakPosCLM P)).toContinuousLinearMap‖
    exact hnorm

private theorem exists_orthogonal_decomposition_with_support
    {M P : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] [WStarAlgebra M]
    [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]
    (f : σ(M, P) →L[ℂ] ℂ) (hf : IsSelfAdjoint (WithConv.toConv f)) :
    ∃ (f₁ f₂ : M →ₚ[ℂ] ℂ)
        (hf₁ : f₁.IsNormalOnProjections) (hf₂ : f₂.IsNormalOnProjections),
      f.comp (toUltraweakL ℂ M P) =
          f₁.toContinuousLinearMap - f₂.toContinuousLinearMap ∧
        ‖f.comp (toUltraweakL ℂ M P)‖ =
          ‖f₁.toContinuousLinearMap‖ + ‖f₂.toContinuousLinearMap‖ ∧
        (f₁.support hf₁).1 * (f₂.support hf₂).1 = 0 := by
  obtain ⟨p, f₁, f₂, hf₁, hf₂, hdecomp, hnorm, hcarrier₁, hcarrier₂⟩ :=
    exists_orthogonal_decomposition_with_carrier f hf
  have hs₁p : f₁.support hf₁ ≤ p :=
    (f₁.support_le_iff_apply_eq_apply_one hf₁ p).2 hcarrier₁
  let q : {q : M // IsStarProjection q} := ⟨1 - p.1, p.2.one_sub⟩
  have hs₂q : f₂.support hf₂ ≤ q :=
    (f₂.support_le_iff_apply_eq_apply_one hf₂ q).2 hcarrier₂
  have hs₁_mul_p : (f₁.support hf₁).1 * p.1 = (f₁.support hf₁).1 :=
    ((f₁.support hf₁).2.le_iff_mul_eq_left p.2).mp hs₁p
  have hq_mul_s₂ : q.1 * (f₂.support hf₂).1 = (f₂.support hf₂).1 :=
    ((f₂.support hf₂).2.le_iff_mul_eq_right q.2).mp hs₂q
  have hp_mul_s₂ : p.1 * (f₂.support hf₂).1 = 0 := by
    calc
      p.1 * (f₂.support hf₂).1 = p.1 * (q.1 * (f₂.support hf₂).1) := by
        rw [hq_mul_s₂]
      _ = (p.1 * q.1) * (f₂.support hf₂).1 := by rw [mul_assoc]
      _ = 0 := by simp [q, p.2.mul_one_sub_self]
  have hsupport : (f₁.support hf₁).1 * (f₂.support hf₂).1 = 0 := by
    calc
      (f₁.support hf₁).1 * (f₂.support hf₂).1 =
          ((f₁.support hf₁).1 * p.1) * (f₂.support hf₂).1 := by
            rw [hs₁_mul_p]
      _ = (f₁.support hf₁).1 *
          (p.1 * (f₂.support hf₂).1) := by rw [mul_assoc]
      _ = 0 := by rw [hp_mul_s₂, mul_zero]
  exact ⟨f₁, f₂, hf₁, hf₂, hdecomp, hnorm, hsupport⟩

private lemma component_norms_eq_of_sub_eq_of_norm_sum
    {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
    (f₁ f₂ g₁ g₂ : M →ₚ[ℂ] ℂ)
    (hsub : f₁.toContinuousLinearMap - f₂.toContinuousLinearMap =
      g₁.toContinuousLinearMap - g₂.toContinuousLinearMap)
    (hsum : ‖f₁.toContinuousLinearMap‖ + ‖f₂.toContinuousLinearMap‖ =
      ‖g₁.toContinuousLinearMap‖ + ‖g₂.toContinuousLinearMap‖) :
    ‖f₁.toContinuousLinearMap‖ = ‖g₁.toContinuousLinearMap‖ ∧
      ‖f₂.toContinuousLinearMap‖ = ‖g₂.toContinuousLinearMap‖ := by
  have hsub_one := congrArg (fun f : M →L[ℂ] ℂ ↦ f 1) hsub
  have hdiff : ‖f₁.toContinuousLinearMap‖ - ‖f₂.toContinuousLinearMap‖ =
      ‖g₁.toContinuousLinearMap‖ - ‖g₂.toContinuousLinearMap‖ := by
    have hc : ((‖f₁.toContinuousLinearMap‖ : ℝ) : ℂ) -
        ((‖f₂.toContinuousLinearMap‖ : ℝ) : ℂ) =
        ((‖g₁.toContinuousLinearMap‖ : ℝ) : ℂ) -
          ((‖g₂.toContinuousLinearMap‖ : ℝ) : ℂ) := by
      calc
        ((‖f₁.toContinuousLinearMap‖ : ℝ) : ℂ) -
            ((‖f₂.toContinuousLinearMap‖ : ℝ) : ℂ) = f₁ 1 - f₂ 1 := by
          rw [PositiveContinuousLinearMap.ofReal_opNorm_eq_map_one
            f₁.toPositiveContinuousLinearMap,
            PositiveContinuousLinearMap.ofReal_opNorm_eq_map_one
              f₂.toPositiveContinuousLinearMap]
          rfl
        _ = g₁ 1 - g₂ 1 := by
          simpa only [sub_apply, PositiveLinearMap.toContinuousLinearMap_apply] using hsub_one
        _ = ((‖g₁.toContinuousLinearMap‖ : ℝ) : ℂ) -
            ((‖g₂.toContinuousLinearMap‖ : ℝ) : ℂ) := by
          rw [PositiveContinuousLinearMap.ofReal_opNorm_eq_map_one
            g₁.toPositiveContinuousLinearMap,
            PositiveContinuousLinearMap.ofReal_opNorm_eq_map_one
              g₂.toPositiveContinuousLinearMap]
          rfl
    exact_mod_cast hc
  constructor <;> linarith

private lemma apply_cutdown_eq_zero_of_support_le_one_sub
    {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] [WStarAlgebra M]
    (φ : M →ₚ[ℂ] ℂ) (hφ : φ.IsNormalOnProjections)
    (p : {p : M // IsStarProjection p})
    (hsp : φ.support hφ ≤ ⟨1 - p.1, p.2.one_sub⟩) (x : M) :
    φ (p.1 * x * p.1) = 0 := by
  let s := φ.support hφ
  have hsp_zero : s.1 * p.1 = 0 :=
    (s.2.mul_eq_zero_iff_le_one_sub p.2).mpr hsp
  have hps_zero : p.1 * s.1 = 0 := by
    simpa only [star_mul, s.2.isSelfAdjoint.star_eq, p.2.isSelfAdjoint.star_eq,
      star_zero] using congrArg star hsp_zero
  calc
    φ (p.1 * x * p.1) = φ (s.1 * (p.1 * x * p.1) * s.1) :=
      (φ.apply_support_mul_support hφ _).symm
    _ = φ 0 := by
      congr 1
      calc
        s.1 * (p.1 * x * p.1) * s.1 =
            (s.1 * p.1) * x * (p.1 * s.1) := by noncomm_ring
        _ = 0 := by rw [hsp_zero, hps_zero]; simp
    _ = 0 := map_zero φ

private theorem orthogonal_decomposition_unique_of_complementary_carrier
    {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] [WStarAlgebra M]
    (p : {p : M // IsStarProjection p})
    (f₁ f₂ g₁ g₂ : M →ₚ[ℂ] ℂ)
    (hf₁ : f₁.IsNormalOnProjections) (hf₂ : f₂.IsNormalOnProjections)
    (hg₁ : g₁.IsNormalOnProjections) (hg₂ : g₂.IsNormalOnProjections)
    (hf₁p : f₁ p.1 = f₁ 1) (hf₂p : f₂ (1 - p.1) = f₂ 1)
    (hsub : f₁.toContinuousLinearMap - f₂.toContinuousLinearMap =
      g₁.toContinuousLinearMap - g₂.toContinuousLinearMap)
    (hnormf : ‖f₁.toContinuousLinearMap - f₂.toContinuousLinearMap‖ =
      ‖f₁.toContinuousLinearMap‖ + ‖f₂.toContinuousLinearMap‖)
    (hnormg : ‖g₁.toContinuousLinearMap - g₂.toContinuousLinearMap‖ =
      ‖g₁.toContinuousLinearMap‖ + ‖g₂.toContinuousLinearMap‖) :
    f₁ = g₁ ∧ f₂ = g₂ := by
  let q : {q : M // IsStarProjection q} := ⟨1 - p.1, p.2.one_sub⟩
  have hf₂p_zero : f₂ p.1 = 0 := by
    have h := hf₂p
    rw [map_sub] at h
    exact sub_eq_self.mp h
  have hf₁_support : f₁.support hf₁ ≤ p :=
    (f₁.support_le_iff_apply_eq_apply_one hf₁ p).mpr hf₁p
  have hf₂_support : f₂.support hf₂ ≤ q :=
    (f₂.support_le_iff_apply_eq_apply_one hf₂ q).mpr hf₂p
  have hsum : ‖f₁.toContinuousLinearMap‖ + ‖f₂.toContinuousLinearMap‖ =
      ‖g₁.toContinuousLinearMap‖ + ‖g₂.toContinuousLinearMap‖ := by
    rw [← hnormf, hsub, hnormg]
  obtain ⟨hnorm₁, -⟩ :=
    component_norms_eq_of_sub_eq_of_norm_sum f₁ f₂ g₁ g₂ hsub hsum
  have hone₁ : f₁ 1 = g₁ 1 := by
    calc
      f₁ 1 = (‖f₁.toContinuousLinearMap‖ : ℂ) :=
        (PositiveContinuousLinearMap.ofReal_opNorm_eq_map_one
          f₁.toPositiveContinuousLinearMap).symm
      _ = (‖g₁.toContinuousLinearMap‖ : ℂ) := by rw [hnorm₁]
      _ = g₁ 1 := PositiveContinuousLinearMap.ofReal_opNorm_eq_map_one
        g₁.toPositiveContinuousLinearMap
  have hsub_p := congrArg (fun f : M →L[ℂ] ℂ ↦ f p.1) hsub
  have hgeq : g₁ 1 = g₁ p.1 - g₂ p.1 := by
    calc
      g₁ 1 = f₁ 1 := hone₁.symm
      _ = f₁ p.1 := hf₁p.symm
      _ = f₁ p.1 - f₂ p.1 := by rw [hf₂p_zero, sub_zero]
      _ = g₁ p.1 - g₂ p.1 := by
        simpa only [sub_apply, PositiveLinearMap.toContinuousLinearMap_apply] using hsub_p
  have hg₁p_le : g₁ p.1 ≤ g₁ 1 := g₁.monotone p.2.le_one
  have hone_le_hg₁p : g₁ 1 ≤ g₁ p.1 := by
    rw [hgeq]
    exact sub_le_self _ (g₂.map_nonneg p.2.nonneg)
  have hg₁p : g₁ p.1 = g₁ 1 := hg₁p_le.antisymm hone_le_hg₁p
  have hg₂p_zero : g₂ p.1 = 0 := by
    apply sub_eq_self.mp
    calc
      g₁ 1 - g₂ p.1 = g₁ p.1 - g₂ p.1 := by rw [hg₁p]
      _ = g₁ 1 := hgeq.symm
  have hg₁_support : g₁.support hg₁ ≤ p :=
    (g₁.support_le_iff_apply_eq_apply_one hg₁ p).mpr hg₁p
  have hg₂q : g₂ q.1 = g₂ 1 := by
    change g₂ (1 - p.1) = g₂ 1
    rw [map_sub, hg₂p_zero, sub_zero]
  have hg₂_support : g₂.support hg₂ ≤ q :=
    (g₂.support_le_iff_apply_eq_apply_one hg₂ q).mpr hg₂q
  have hf₁_eq : f₁ = g₁ := by
    ext x
    calc
      f₁ x = f₁ (p.1 * x * p.1) :=
        (f₁.apply_cutdown_of_support_le hf₁ p hf₁_support x).symm
      _ = f₁ (p.1 * x * p.1) - f₂ (p.1 * x * p.1) := by
        rw [apply_cutdown_eq_zero_of_support_le_one_sub
          f₂ hf₂ p hf₂_support x, sub_zero]
      _ = g₁ (p.1 * x * p.1) - g₂ (p.1 * x * p.1) := by
        have hx := congrArg (fun f : M →L[ℂ] ℂ ↦ f (p.1 * x * p.1)) hsub
        simpa only [sub_apply, PositiveLinearMap.toContinuousLinearMap_apply] using hx
      _ = g₁ (p.1 * x * p.1) := by
        rw [apply_cutdown_eq_zero_of_support_le_one_sub
          g₂ hg₂ p hg₂_support x, sub_zero]
      _ = g₁ x := g₁.apply_cutdown_of_support_le hg₁ p hg₁_support x
  refine ⟨hf₁_eq, ?_⟩
  ext x
  have hx := congrArg (fun f : M →L[ℂ] ℂ ↦ f x) hsub
  rw [hf₁_eq] at hx
  have hx' : g₁ x - f₂ x = g₁ x - g₂ x := by
    simpa only [sub_apply, PositiveLinearMap.toContinuousLinearMap_apply] using hx
  exact sub_right_inj.mp hx'

private theorem exists_selfAdjoint_ultraweak_rep_sub
    {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] [WStarAlgebra M]
    (phi psi : M →ₚ[ℂ] ℂ)
    (hphi : phi.IsNormalOnProjections) (hpsi : psi.IsNormalOnProjections) :
    ∃ f : σ(M, WStarAlgebra.predual M) →L[ℂ] ℂ,
      IsSelfAdjoint (WithConv.toConv f) ∧
        f.comp (toUltraweakL ℂ M (WStarAlgebra.predual M)) =
          phi.toContinuousLinearMap - psi.toContinuousLinearMap := by
  have hphi_mem : phi.toContinuousLinearMap ∈
      continuousDual ℂ M (WStarAlgebra.predual M) :=
    (phi.isNormalOnProjections_iff_mem_continuousDual
      (P := WStarAlgebra.predual M)).mp hphi
  have hpsi_mem : psi.toContinuousLinearMap ∈
      continuousDual ℂ M (WStarAlgebra.predual M) :=
    (psi.isNormalOnProjections_iff_mem_continuousDual
      (P := WStarAlgebra.predual M)).mp hpsi
  obtain ⟨phiSigma, hphiSigma⟩ :=
    (mem_continuousDual_iff_exists_comp_toUltraweakL
      (P := WStarAlgebra.predual M) phi.toContinuousLinearMap).mp hphi_mem
  obtain ⟨psiSigma, hpsiSigma⟩ :=
    (mem_continuousDual_iff_exists_comp_toUltraweakL
      (P := WStarAlgebra.predual M) psi.toContinuousLinearMap).mp hpsi_mem
  let f : σ(M, WStarAlgebra.predual M) →L[ℂ] ℂ := phiSigma - psiSigma
  have hphiSigma_apply (x : σ(M, WStarAlgebra.predual M)) :
      phiSigma x = phi (ofUltraweak x) := by
    have hx := congrArg (fun g : M →L[ℂ] ℂ ↦ g (ofUltraweak x)) hphiSigma
    simpa only [ContinuousLinearMap.comp_apply, toUltraweakL_apply,
      toUltraweak_ofUltraweak, PositiveLinearMap.toContinuousLinearMap_apply] using hx
  have hpsiSigma_apply (x : σ(M, WStarAlgebra.predual M)) :
      psiSigma x = psi (ofUltraweak x) := by
    have hx := congrArg (fun g : M →L[ℂ] ℂ ↦ g (ofUltraweak x)) hpsiSigma
    simpa only [ContinuousLinearMap.comp_apply, toUltraweakL_apply,
      toUltraweak_ofUltraweak, PositiveLinearMap.toContinuousLinearMap_apply] using hx
  refine ⟨f, ?_, ?_⟩
  · rw [ContinuousLinearMap.IntrinsicStar.isSelfAdjoint_iff_map_star]
    intro x
    change phiSigma (star x) - psiSigma (star x) =
      star (phiSigma x - psiSigma x)
    rw [hphiSigma_apply, hpsiSigma_apply, ofUltraweak_star,
      map_star, map_star, star_sub, hphiSigma_apply, hpsiSigma_apply]
  · rw [show f = phiSigma - psiSigma by rfl, ContinuousLinearMap.sub_comp,
      hphiSigma, hpsiSigma]

/-- A self-adjoint normal functional has a unique decomposition as the difference of two
orthogonal normal positive functionals. This is Sakai, Theorem 1.14.3. -/
theorem existsUnique_orthogonal_decomposition_of_isSelfAdjoint
    {M P : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] [WStarAlgebra M]
    [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]
    (f : σ(M, P) →L[ℂ] ℂ) (hf : IsSelfAdjoint (WithConv.toConv f)) :
    ∃! parts : (M →ₚ[ℂ] ℂ) × (M →ₚ[ℂ] ℂ),
      parts.1.IsNormalOnProjections ∧ parts.2.IsNormalOnProjections ∧
        f.comp (toUltraweakL ℂ M P) =
          parts.1.toContinuousLinearMap - parts.2.toContinuousLinearMap ∧
        parts.1.IsOrthogonal parts.2 := by
  obtain ⟨p, f₁, f₂, hf₁, hf₂, hdecomp, hnorm, hf₁p, hf₂p⟩ :=
    exists_orthogonal_decomposition_with_carrier f hf
  refine ⟨⟨f₁, f₂⟩, ⟨hf₁, hf₂, hdecomp, ?_⟩, ?_⟩
  · rw [PositiveLinearMap.IsOrthogonal, ← hdecomp]
    exact hnorm
  · rintro ⟨g₁, g₂⟩ ⟨hg₁, hg₂, hgdecomp, hgorth⟩
    have hpair := orthogonal_decomposition_unique_of_complementary_carrier
      p f₁ f₂ g₁ g₂ hf₁ hf₂ hg₁ hg₂ hf₁p hf₂p
      (hdecomp.symm.trans hgdecomp) (by rw [← hdecomp]; exact hnorm) hgorth
    exact Prod.ext hpair.1.symm hpair.2.symm

/-- Sakai's norm orthogonality of normal positive functionals forces their support projections
to be orthogonal. The proof applies the Jordan-decomposition uniqueness theorem to their
difference; it does not assume this support characterization in that uniqueness proof. -/
theorem _root_.PositiveLinearMap.support_mul_eq_zero_of_isOrthogonal
    {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] [WStarAlgebra M]
    (phi psi : M →ₚ[ℂ] ℂ)
    (hphi : phi.IsNormalOnProjections) (hpsi : psi.IsNormalOnProjections)
    (horth : phi.IsOrthogonal psi) :
    (phi.support hphi).1 * (psi.support hpsi).1 = 0 := by
  obtain ⟨f, hf, hfcomp⟩ :=
    exists_selfAdjoint_ultraweak_rep_sub phi psi hphi hpsi
  obtain ⟨f₁, f₂, hf₁, hf₂, hdecomp, -, hsupport⟩ :=
    exists_orthogonal_decomposition_with_support f hf
  obtain ⟨parts, -, hunique⟩ :=
    existsUnique_orthogonal_decomposition_of_isSelfAdjoint f hf
  have hcanonical : (f₁, f₂) = parts :=
    hunique (f₁, f₂) ⟨hf₁, hf₂, hdecomp,
      f₁.isOrthogonal_of_support_mul_eq_zero f₂ hf₁ hf₂ hsupport⟩
  have hgiven : (phi, psi) = parts :=
    hunique (phi, psi) ⟨hphi, hpsi, hfcomp, horth⟩
  have hpairs : (phi, psi) = (f₁, f₂) := hgiven.trans hcanonical.symm
  have hphi_eq : phi = f₁ := congrArg Prod.fst hpairs
  have hpsi_eq : psi = f₂ := congrArg Prod.snd hpairs
  simpa [hphi_eq, hpsi_eq] using hsupport

/-- For normal positive functionals on a $W^*$-algebra, Sakai's norm orthogonality is equivalent
to orthogonality of the support projections. -/
theorem _root_.PositiveLinearMap.isOrthogonal_iff_support_mul_eq_zero
    {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] [WStarAlgebra M]
    (phi psi : M →ₚ[ℂ] ℂ)
    (hphi : phi.IsNormalOnProjections) (hpsi : psi.IsNormalOnProjections) :
    phi.IsOrthogonal psi ↔
      (phi.support hphi).1 * (psi.support hpsi).1 = 0 :=
  ⟨phi.support_mul_eq_zero_of_isOrthogonal psi hphi hpsi,
    phi.isOrthogonal_of_support_mul_eq_zero psi hphi hpsi⟩

end

end Ultraweak
