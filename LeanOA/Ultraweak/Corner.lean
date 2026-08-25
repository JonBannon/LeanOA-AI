module

public import LeanOA.CStarAlgebra.Corner
public import LeanOA.Mathlib.Analysis.CStarAlgebra.Basic
public import LeanOA.Ultraweak.Algebra
public import LeanOA.Ultraweak.ContinuousStar
public import LeanOA.Ultraweak.WStarAlgebra
public import Mathlib.Analysis.CStarAlgebra.SpecialFunctions.PosPart

@[expose] public section

/-!
# Corners in the ultraweak topology

This file realizes a projection corner as an explicit linear subspace of an ambient W⋆-algebra
with chosen predual. The interface uses bundled maps between the normed corner and the ambient
ultraweak space; no client needs to unfold either type synonym.
-/

open scoped ComplexStarModule Pointwise Ultraweak
open Filter Set

universe u v

namespace IsStarProjection.Corner

variable {M : Type u} {P : Type v} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]
  {p : M} (hp : IsStarProjection p)

private lemma realPart_cutdownL_eq_zero_of_norm_shift_le
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {p a : A} (hp : IsStarProjection p)
    (h : ∀ n : ℕ, max ‖a + (n : ℂ) • p‖ ‖a - (n : ℂ) • p‖ ≤ √(1 + n ^ 2)) :
    ℜ (cutdownL hp a) = 0 := by
  apply Subtype.ext
  apply CFC.eq_zero_of_spectrum_subset_zero (R := ℝ) _ fun c hc ↦ ?_
  rw [Set.mem_singleton_iff, ← abs_eq_zero]
  refine le_antisymm ?_ (abs_nonneg c)
  refine ge_of_tendsto'
    (Real.tendsto_sqrt_one_add_sq_sub_self_atTop.comp tendsto_natCast_atTop_atTop) fun n ↦ ?_
  rw [Function.comp_apply, le_sub_iff_add_le]
  grw [IsSelfAdjoint.max_norm_add_sub_algebraMap_ge
    (ℜ (cutdownL hp a)).2 c hc n (by positivity)]
  refine (max_le_max ?_ ?_).trans (h n)
  · calc
      ‖(ℜ (cutdownL hp a) : hp.Corner) + algebraMap ℝ hp.Corner n‖ ≤
          ‖cutdownL hp a + algebraMap ℝ hp.Corner n‖ := by
        rw [← norm_coe hp, ← norm_coe hp]
        simp only [coe_add, coe_realPart, coe_cutdownL, coe_algebraMap_real]
        have hn : IsSelfAdjoint (((n : ℝ) : ℂ) • p) := by
          rw [isSelfAdjoint_iff]
          simp [hp.isSelfAdjoint.star_eq]
        rw [← hn.coe_realPart]
        change ‖((ℜ (p * a * p) + ℜ (((n : ℝ) : ℂ) • p) : selfAdjoint A) : A)‖ ≤ _
        rw [← map_add, AddSubgroup.norm_coe]
        simpa only [hn.coe_realPart] using
          realPart.norm_le (p * a * p + ((n : ℝ) : ℂ) • p)
      _ = ‖p * (a + (n : ℂ) • p) * p‖ := by
        rw [← norm_coe hp, coe_add, coe_cutdownL, coe_algebraMap_real]
        simp [mul_add, add_mul, hp.isIdempotentElem.eq]
      _ ≤ ‖a + (n : ℂ) • p‖ := by
        simpa only [← norm_coe hp, coe_cutdownL] using
          norm_cutdownL_le hp (a + (n : ℂ) • p)
  · calc
      ‖(ℜ (cutdownL hp a) : hp.Corner) - algebraMap ℝ hp.Corner n‖ ≤
          ‖cutdownL hp a - algebraMap ℝ hp.Corner n‖ := by
        rw [← norm_coe hp, ← norm_coe hp]
        simp only [coe_sub, coe_realPart, coe_cutdownL, coe_algebraMap_real]
        have hn : IsSelfAdjoint (((n : ℝ) : ℂ) • p) := by
          rw [isSelfAdjoint_iff]
          simp [hp.isSelfAdjoint.star_eq]
        rw [← hn.coe_realPart]
        change ‖((ℜ (p * a * p) - ℜ (((n : ℝ) : ℂ) • p) : selfAdjoint A) : A)‖ ≤ _
        rw [← map_sub, AddSubgroup.norm_coe]
        simpa only [hn.coe_realPart] using
          realPart.norm_le (p * a * p - ((n : ℝ) : ℂ) • p)
      _ = ‖p * (a - (n : ℂ) • p) * p‖ := by
        rw [← norm_coe hp, coe_sub, coe_cutdownL, coe_algebraMap_real]
        simp [mul_sub, sub_mul, hp.isIdempotentElem.eq]
      _ ≤ ‖a - (n : ℂ) • p‖ := by
        simpa only [← norm_coe hp, coe_cutdownL] using
          norm_cutdownL_le hp (a - (n : ℂ) • p)

private lemma imaginaryPart_cutdownL_eq_zero_of_norm_shift_le
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {p a : A} (hp : IsStarProjection p)
    (h : ∀ n : ℕ,
      max ‖a + ((n : ℂ) * Complex.I) • p‖ ‖a - ((n : ℂ) * Complex.I) • p‖ ≤
        √(1 + n ^ 2)) :
    ℑ (cutdownL hp a) = 0 := by
  have hreal := realPart_cutdownL_eq_zero_of_norm_shift_le (a := -Complex.I • a) hp
    fun n ↦ ?_
  · rw [map_smul] at hreal
    have heq : ℜ (-Complex.I • cutdownL hp a) = ℑ (cutdownL hp a) := by
      simp only [neg_smul, map_neg, realPart_I_smul, neg_neg]
    rwa [heq] at hreal
  · rw [max_le_iff]
    refine ⟨?_, ?_⟩
    · rw [show -Complex.I • a + (n : ℂ) • p =
          -Complex.I • (a + ((n : ℂ) * Complex.I) • p) by
          have hnI : -(Complex.I * ((n : ℂ) * Complex.I)) = (n : ℂ) := by
            rw [show Complex.I * ((n : ℂ) * Complex.I) =
              (n : ℂ) * (Complex.I * Complex.I) by ac_rfl, Complex.I_mul_I]
            simp
          rw [smul_add, smul_smul, neg_mul, hnI], norm_smul]
      simpa using (max_le_iff.mp (h n)).1
    · rw [show -Complex.I • a - (n : ℂ) • p =
          -Complex.I • (a - ((n : ℂ) * Complex.I) • p) by
          have hnI : -(Complex.I * ((n : ℂ) * Complex.I)) = (n : ℂ) := by
            rw [show Complex.I * ((n : ℂ) * Complex.I) =
              (n : ℂ) * (Complex.I * Complex.I) by ac_rfl, Complex.I_mul_I]
            simp
          rw [smul_sub, smul_smul, neg_mul, hnI], norm_smul]
      simpa using (max_le_iff.mp (h n)).2

private lemma cutdownL_eq_zero_of_norm_shift_le
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {p a : A} (hp : IsStarProjection p)
    (hre : ∀ n : ℕ, max ‖a + (n : ℂ) • p‖ ‖a - (n : ℂ) • p‖ ≤ √(1 + n ^ 2))
    (him : ∀ n : ℕ,
      max ‖a + ((n : ℂ) * Complex.I) • p‖ ‖a - ((n : ℂ) * Complex.I) • p‖ ≤
        √(1 + n ^ 2)) :
    cutdownL hp a = 0 := by
  rw [← realPart_add_I_smul_imaginaryPart (cutdownL hp a),
    realPart_cutdownL_eq_zero_of_norm_shift_le hp hre,
    imaginaryPart_cutdownL_eq_zero_of_norm_shift_le hp him]
  simp

private lemma cutdownL_eq_zero_of_norm_add_smul_le
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {p a : A} (hp : IsStarProjection p)
    (h : ∀ z : ℂ, ‖a + z • p‖ ≤ √(1 + ‖z‖ ^ 2)) : cutdownL hp a = 0 := by
  apply cutdownL_eq_zero_of_norm_shift_le hp
  · intro n
    rw [max_le_iff]
    exact ⟨by simpa using h n, by simpa [sub_eq_add_neg] using h (-n)⟩
  · intro n
    rw [max_le_iff]
    exact ⟨by simpa [norm_mul] using h (n * Complex.I),
      by simpa [sub_eq_add_neg, norm_mul] using h (-(n * Complex.I))⟩

private lemma norm_offDiagonal_add_smul_left_le
    {A : Type*} [CStarAlgebra A]
    {p x : A} (hp : IsStarProjection p) (hxnorm : ‖x‖ ≤ 1) (z : ℂ) :
    ‖p * x * (1 - p) + z • p‖ ≤ √(1 + ‖z‖ ^ 2) := by
  refine (CStarRing.norm_add_le_sqrt_of_mul_star_eq_zero ?_).trans ?_
  · simp [star_smul, hp.isSelfAdjoint.star_eq, mul_assoc, hp.one_sub_mul_self]
  · gcongr
    · exact (sq_le_one_iff₀ (norm_nonneg _)).2 <| (hp.norm_mul_one_sub_le x).trans hxnorm
    · simpa only [norm_smul, mul_one] using
        mul_le_mul_of_nonneg_left (IsStarProjection.norm_le p hp) (norm_nonneg z)

private lemma norm_offDiagonal_add_smul_right_le
    {A : Type*} [CStarAlgebra A]
    {p x : A} (hp : IsStarProjection p) (hx : IsSelfAdjoint x) (hxnorm : ‖x‖ ≤ 1)
    (z : ℂ) :
    ‖p * x * (1 - p) + z • (1 - p)‖ ≤ √(1 + ‖z‖ ^ 2) := by
  rw [← norm_star]
  simpa [star_add, star_smul, star_mul, hx.star_eq, hp.isSelfAdjoint.star_eq, mul_assoc,
    hp.one_sub.isSelfAdjoint.star_eq] using
    norm_offDiagonal_add_smul_left_le hp.one_sub hxnorm (star z)

/-- The upper off-diagonal contractions obtained from self-adjoint contractions. This is an
auxiliary set in Sakai's closed-kernel argument. -/
private def upperOffDiagonalUnit : Set σ(M, P) :=
  {a | ∃ x : M, IsSelfAdjoint x ∧ ‖x‖ ≤ 1 ∧
    a = toUltraweak ℂ P (p * x * (1 - p))}

private lemma norm_add_le_of_mem_closure
    {𝕜 E Q : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup Q] [NormedSpace 𝕜 Q] [Predual 𝕜 E Q]
    {s : Set (Ultraweak 𝕜 E Q)} {x : Ultraweak 𝕜 E Q}
    (hx : x ∈ closure s) (a : E) (r : ℝ)
    (h : ∀ y ∈ s, ‖ofUltraweak y + a‖ ≤ r) : ‖ofUltraweak x + a‖ ≤ r := by
  simpa [Metric.mem_closedBall, dist_eq_norm] using closure_minimal
    (fun y hy ↦ by simpa [Metric.mem_closedBall, dist_eq_norm] using h y hy)
    (Ultraweak.isClosed_closedBall 𝕜 Q (-a) r) hx

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace P] in
private lemma norm_add_smul_left_le_of_mem_closure_upperOffDiagonalUnit
    (hp : IsStarProjection p) {a : σ(M, P)}
    (ha : a ∈ closure (upperOffDiagonalUnit (P := P) (p := p))) (z : ℂ) :
    ‖ofUltraweak a + z • p‖ ≤ √(1 + ‖z‖ ^ 2) := by
  apply norm_add_le_of_mem_closure ha
  rintro _ ⟨x, -, hxnorm, rfl⟩
  exact norm_offDiagonal_add_smul_left_le hp hxnorm z

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace P] in
private lemma norm_add_smul_right_le_of_mem_closure_upperOffDiagonalUnit
    (hp : IsStarProjection p) {a : σ(M, P)}
    (ha : a ∈ closure (upperOffDiagonalUnit (P := P) (p := p))) (z : ℂ) :
    ‖ofUltraweak a + z • (1 - p)‖ ≤ √(1 + ‖z‖ ^ 2) := by
  apply norm_add_le_of_mem_closure ha
  rintro _ ⟨x, hx, hxnorm, rfl⟩
  exact norm_offDiagonal_add_smul_right_le hp hx hxnorm z

omit [CompleteSpace P] in
private lemma cutdowns_eq_zero_of_mem_closure_upperOffDiagonalUnit
    (hp : IsStarProjection p) {a : σ(M, P)}
    (ha : a ∈ closure (upperOffDiagonalUnit (P := P) (p := p))) :
    p * ofUltraweak a * p = 0 ∧
      (1 - p) * ofUltraweak a * (1 - p) = 0 := by
  exact ⟨by simpa using congrArg (inclusionL hp) <|
      cutdownL_eq_zero_of_norm_add_smul_le hp fun z ↦
        norm_add_smul_left_le_of_mem_closure_upperOffDiagonalUnit hp ha z,
    by simpa using congrArg (inclusionL hp.one_sub) <|
      cutdownL_eq_zero_of_norm_add_smul_le hp.one_sub fun z ↦
        norm_add_smul_right_le_of_mem_closure_upperOffDiagonalUnit hp ha z⟩

omit [CompleteSpace P] in
private lemma lowerOffDiagonal_eq_zero_of_mem_closure_upperOffDiagonalUnit
    (hp : IsStarProjection p) {a : σ(M, P)}
    (ha : a ∈ closure (upperOffDiagonalUnit (P := P) (p := p))) :
    (1 - p) * ofUltraweak a * p = 0 := by
  let c := (1 - p) * ofUltraweak a * p
  by_contra hc
  have hc_pos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (‖c‖⁻¹)
  have hn : 1 < n * ‖c‖ := by
    rw [← div_lt_iff₀ hc_pos, one_div]
    exact hn
  have ha_norm : ‖ofUltraweak a‖ ≤ 1 := by
    simpa using norm_add_smul_left_le_of_mem_closure_upperOffDiagonalUnit hp ha 0
  have hb_norm : ‖p * ofUltraweak a * (1 - p)‖ ≤ 1 :=
    (hp.norm_mul_one_sub_le _).trans ha_norm
  have horth (x : M) (z : ℂ) :
      ‖p * x * (1 - p) + z • c‖ = max ‖p * x * (1 - p)‖ (‖z‖ * ‖c‖) := by
    exact hp.norm_mul_one_sub_add_smul_one_sub_mul_eq_max x (ofUltraweak a) z
  have hle : ‖ofUltraweak a + (n : ℂ) • c‖ ≤ n * ‖c‖ := by
    apply norm_add_le_of_mem_closure ha
    rintro _ ⟨x, -, hx_norm, rfl⟩
    simp only [ofUltraweak_toUltraweak]
    rw [horth]
    simp only [norm_natCast]
    exact max_le ((hp.norm_mul_one_sub_le x).trans hx_norm |>.trans hn.le) le_rfl
  have heq : ‖ofUltraweak a + (n : ℂ) • c‖ = (n + 1) * ‖c‖ := by
    rw [show ofUltraweak a = p * ofUltraweak a * (1 - p) + c by
      dsimp [c]
      have hdiag := cutdowns_eq_zero_of_mem_closure_upperOffDiagonalUnit
        (P := P) hp ha
      calc
        ofUltraweak a = p * ofUltraweak a * p + p * ofUltraweak a * (1 - p) +
            (1 - p) * ofUltraweak a * p + (1 - p) * ofUltraweak a * (1 - p) :=
          peirce_decomposition p _
        _ = p * ofUltraweak a * (1 - p) + (1 - p) * ofUltraweak a * p := by
          rw [hdiag.1, hdiag.2]
          simp]
    rw [add_assoc, show c + (n : ℂ) • c = ((n + 1 : ℕ) : ℂ) • c by
      module, horth]
    rw [norm_natCast]
    have hlarge : ‖p * ofUltraweak a * (1 - p)‖ ≤ (n + 1 : ℕ) * ‖c‖ := by
      rw [Nat.cast_add, Nat.cast_one]
      nlinarith
    rw [max_eq_right hlarge]
    norm_num [Nat.cast_add]
  rw [heq] at hle
  nlinarith [norm_pos_iff.mpr hc]

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace P] in
private lemma isCompact_closure_upperOffDiagonalUnit (hp : IsStarProjection p) :
    IsCompact (closure (upperOffDiagonalUnit (P := P) (p := p))) := by
  refine (Ultraweak.isCompact_closedBall ℂ P (0 : M) 1).of_isClosed_subset
    isClosed_closure <| closure_minimal ?_ (Ultraweak.isClosed_closedBall ℂ P (0 : M) 1)
  rintro _ ⟨x, -, hxnorm, rfl⟩
  simpa [Metric.mem_closedBall, dist_zero_right] using
    norm_offDiagonal_add_smul_left_le hp hxnorm 0

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace P] in
private lemma upperOffDiagonal_mem_upperOffDiagonalUnit (hp : IsStarProjection p)
    {a : M} (ha : ‖a‖ ≤ 1) :
    toUltraweak ℂ P (p * a * (1 - p)) ∈ upperOffDiagonalUnit (P := P) (p := p) := by
  obtain ⟨x, hx, hxnorm, hxp⟩ := hp.exists_isSelfAdjoint_norm_eq_mul_one_sub a
  refine ⟨x, hx, hxnorm.le.trans (hp.norm_mul_one_sub_le a) |>.trans ha, ?_⟩
  rw [toUltraweak_inj]
  exact hxp.symm

omit [CompleteSpace P] in
private lemma isClosed_upperOffDiagonalUnit (hp : IsStarProjection p) :
    IsClosed (upperOffDiagonalUnit (P := P) (p := p)) := by
  rw [← closure_subset_iff_isClosed]
  intro a ha
  have hdiag := cutdowns_eq_zero_of_mem_closure_upperOffDiagonalUnit (P := P) hp ha
  have hlower := lowerOffDiagonal_eq_zero_of_mem_closure_upperOffDiagonalUnit
    (P := P) hp ha
  have ha_norm : ‖ofUltraweak a‖ ≤ 1 := by
    simpa using norm_add_smul_left_le_of_mem_closure_upperOffDiagonalUnit hp ha 0
  rw [show a = toUltraweak ℂ P (p * ofUltraweak a * (1 - p)) by
    rw [← ofUltraweak_inj]
    simp only [ofUltraweak_toUltraweak]
    calc
      ofUltraweak a = p * ofUltraweak a * p + p * ofUltraweak a * (1 - p) +
          (1 - p) * ofUltraweak a * p + (1 - p) * ofUltraweak a * (1 - p) :=
        peirce_decomposition p _
      _ = p * ofUltraweak a * (1 - p) := by rw [hdiag.1, hdiag.2, hlower]; simp]
  exact upperOffDiagonal_mem_upperOffDiagonalUnit (P := P) hp <|
    ha_norm

omit [CompleteSpace P] in
private lemma isCompact_upperOffDiagonalUnit (hp : IsStarProjection p) :
    IsCompact (upperOffDiagonalUnit (P := P) (p := p)) := by
  rw [← (isClosed_upperOffDiagonalUnit (P := P) hp).closure_eq]
  exact isCompact_closure_upperOffDiagonalUnit (P := P) hp

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace P] in
include hp in
lemma _root_.IsStarProjection.ultraweakMulLeftₗ_idempotent (x : σ(M, P)) :
    Ultraweak.mulLeftₗ (𝕜 := ℂ) (P := P) p
        (Ultraweak.mulLeftₗ (𝕜 := ℂ) (P := P) p x) =
      Ultraweak.mulLeftₗ (𝕜 := ℂ) (P := P) p x := by
  rw [← ofUltraweak_inj]
  simp [← mul_assoc, hp.isIdempotentElem.eq]

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace P] in
include hp in
lemma _root_.IsStarProjection.norm_ultraweakMulLeftₗ_le (x : σ(M, P)) :
    ‖ofUltraweak (Ultraweak.mulLeftₗ (𝕜 := ℂ) (P := P) p x)‖ ≤ ‖ofUltraweak x‖ :=
  (norm_mul_le _ _).trans <| by
    simpa using mul_le_mul_of_nonneg_right (IsStarProjection.norm_le p hp) (norm_nonneg _)

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace P] in
include hp in
lemma _root_.IsStarProjection.mem_range_ultraweakMulLeftₗ_iff {x : σ(M, P)} :
    x ∈ LinearMap.range (Ultraweak.mulLeftₗ (𝕜 := ℂ) (P := P) p) ↔
      p * ofUltraweak x = ofUltraweak x := by
  constructor
  · rintro ⟨y, rfl⟩
    simp [← mul_assoc, hp.isIdempotentElem.eq]
  · intro hx
    exact ⟨x, by rw [← ofUltraweak_inj]; simpa using hx⟩

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace P] in
include hp in
lemma _root_.IsStarProjection.range_ultraweakMulLeftₗ_one_sub :
    LinearMap.range (Ultraweak.mulLeftₗ (𝕜 := ℂ) (P := P) (1 - p)) =
      LinearMap.ker (Ultraweak.mulLeftₗ (𝕜 := ℂ) (P := P) p) := by
  ext x
  rw [hp.one_sub.mem_range_ultraweakMulLeftₗ_iff,
    Ultraweak.mem_ker_mulLeftₗ_iff]
  constructor <;> intro hx
  · calc
      p * ofUltraweak x = ofUltraweak x - (1 - p) * ofUltraweak x := by
        noncomm_ring
      _ = 0 := by rw [hx]; simp
  · calc
      (1 - p) * ofUltraweak x = ofUltraweak x - p * ofUltraweak x := by
        noncomm_ring
      _ = ofUltraweak x := by rw [hx]; simp

/-- The inclusion of a projection corner into its ambient algebra equipped with the ultraweak
topology. -/
noncomputable def ultraweakInclusionₗ : hp.Corner →ₗ[ℂ] σ(M, P) where
  toFun x := toUltraweak ℂ P (x : M)
  map_add' _ _ := by simp
  map_smul' _ _ := rfl

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace P] in
@[simp] lemma ultraweakInclusionₗ_apply (x : hp.Corner) :
    ultraweakInclusionₗ (P := P) hp x = toUltraweak ℂ P (x : M) := rfl

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace P] in
lemma ultraweakInclusionₗ_injective :
    Function.Injective (ultraweakInclusionₗ (P := P) hp) := by
  intro x y h
  apply ext hp
  exact toUltraweak_inj.mp h

/-- The norm-to-ultraweak continuous inclusion of a projection corner into its ambient algebra. -/
noncomputable def ultraweakInclusionL : hp.Corner →L[ℂ] σ(M, P) where
  toLinearMap := ultraweakInclusionₗ (P := P) hp
  cont := (continuous_toUltraweak (𝕜 := ℂ) (M := M) (P := P)).comp
    (inclusionL hp).continuous

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace P] in
@[simp] lemma ultraweakInclusionL_apply (x : hp.Corner) :
    ultraweakInclusionL (P := P) hp x = toUltraweak ℂ P (x : M) := rfl

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace P] in
lemma ultraweakInclusionL_injective :
    Function.Injective (ultraweakInclusionL (P := P) hp) :=
  ultraweakInclusionₗ_injective (P := P) hp

/-- The projection corner as a linear subspace of the ambient algebra with its ultraweak
topology. -/
noncomputable def ultraweakRange : Submodule ℂ σ(M, P) :=
  LinearMap.range (ultraweakInclusionL (P := P) hp).toLinearMap

/-- The ambient linear projection onto a projection corner, with both source and target equipped
with the ultraweak topology. Continuity is established below. -/
noncomputable def ultraweakCutdownₗ : σ(M, P) →ₗ[ℂ] σ(M, P) :=
  (ultraweakInclusionL (P := P) hp).toLinearMap.comp <|
    (cutdownL hp).toLinearMap.comp (Ultraweak.linearEquiv ℂ M P).toLinearMap

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace P] in
@[simp] lemma ultraweakCutdownₗ_apply (x : σ(M, P)) :
    ultraweakCutdownₗ (P := P) hp x = toUltraweak ℂ P (p * ofUltraweak x * p) := rfl

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace P] in
lemma range_ultraweakCutdownₗ :
    LinearMap.range (ultraweakCutdownₗ (P := P) hp) = ultraweakRange (P := P) hp := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact ⟨cutdownL hp (ofUltraweak x), rfl⟩
  · rintro _ ⟨x, rfl⟩
    refine ⟨ultraweakInclusionₗ (P := P) hp x, ?_⟩
    simp [ultraweakCutdownₗ]

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace P] in
lemma mem_ker_ultraweakCutdownₗ_iff {x : σ(M, P)} :
    x ∈ LinearMap.ker (ultraweakCutdownₗ (P := P) hp) ↔ p * ofUltraweak x * p = 0 := by
  rw [LinearMap.mem_ker, ultraweakCutdownₗ_apply, toUltraweak_eq_zero]

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace P] in
lemma ultraweakCutdownₗ_idempotent (x : σ(M, P)) :
    ultraweakCutdownₗ (P := P) hp (ultraweakCutdownₗ (P := P) hp x) =
      ultraweakCutdownₗ (P := P) hp x := by
  rw [← ofUltraweak_inj]
  simp only [ultraweakCutdownₗ_apply, ofUltraweak_toUltraweak]
  simp only [← mul_assoc, hp.isIdempotentElem.eq]
  rw [mul_assoc (p * ofUltraweak x) p p, hp.isIdempotentElem.eq]

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace P] in
/-- Projection cutdown is contractive for the underlying C⋆- norm. -/
lemma norm_ultraweakCutdownₗ_le (x : σ(M, P)) :
    ‖ofUltraweak (ultraweakCutdownₗ (P := P) hp x)‖ ≤ ‖ofUltraweak x‖ := by
  calc
    ‖p * ofUltraweak x * p‖ = ‖cutdownL hp (ofUltraweak x)‖ := by
      rw [← norm_coe hp]
      rfl
    _ ≤ ‖ofUltraweak x‖ := norm_cutdownL_le hp _

omit [CompleteSpace P] in
private lemma mem_ker_ultraweakCutdownₗ_of_mem_closure_upperOffDiagonalUnit
    {x : σ(M, P)} (hx : x ∈ closure (upperOffDiagonalUnit (P := P) (p := p))) :
    x ∈ LinearMap.ker (ultraweakCutdownₗ (P := P) hp) :=
  (mem_ker_ultraweakCutdownₗ_iff (P := P) hp).2 <|
    (cutdowns_eq_zero_of_mem_closure_upperOffDiagonalUnit (P := P) hp hx).1

omit [CompleteSpace P] in
private lemma mem_ker_ultraweakCutdownₗ_of_mem_closure_lowerOffDiagonalUnit
    {x : σ(M, P)}
    (hx : x ∈ closure (upperOffDiagonalUnit (P := P) (p := 1 - p))) :
    x ∈ LinearMap.ker (ultraweakCutdownₗ (P := P) hp) :=
  (mem_ker_ultraweakCutdownₗ_iff (P := P) hp).2 <| by
    simpa using (cutdowns_eq_zero_of_mem_closure_upperOffDiagonalUnit
      (P := P) hp.one_sub hx).2

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace P] in
lemma mem_ultraweakRange_iff {x : σ(M, P)} :
    x ∈ ultraweakRange (P := P) hp ↔
      p * ofUltraweak x = ofUltraweak x ∧ ofUltraweak x * p = ofUltraweak x := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨projection_mul hp y, mul_projection hp y⟩
  · intro hx
    let y := cutdownL hp (ofUltraweak x)
    refine ⟨y, ?_⟩
    rw [← ofUltraweak_inj]
    simp [y, hx.1, hx.2]

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace P] in
lemma ultraweakRange_eq_ofSubmodule :
    ultraweakRange (P := P) hp =
      Ultraweak.ofSubmodule (P := P) (rangeSubmodule hp) := by
  ext x
  rw [mem_ultraweakRange_iff (P := P) hp, Ultraweak.mem_ofSubmodule,
    mem_rangeSubmodule_iff]

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace P] in
private lemma mem_ker_ultraweakCutdownₗ_of_mem_ultraweakRange_one_sub
    {x : σ(M, P)} (hx : x ∈ ultraweakRange (P := P) hp.one_sub) :
    x ∈ LinearMap.ker (ultraweakCutdownₗ (P := P) hp) := by
  rw [mem_ker_ultraweakCutdownₗ_iff (P := P) hp, ← (mem_ultraweakRange_iff
    (P := P) hp.one_sub).mp hx |>.1, ← mul_assoc, hp.mul_one_sub_self]
  simp

include hp in
private lemma isCompact_Icc_zero_projection :
    IsCompact (Icc (0 : σ(M, P)) (toUltraweak ℂ P p)) := by
  refine (Ultraweak.isCompact_closedBall ℂ P (0 : M) 1).of_isClosed_subset isClosed_Icc ?_
  intro x hx
  rw [Set.mem_Icc] at hx
  simp only [mem_preimage, Metric.mem_closedBall, dist_zero_right]
  exact (CStarAlgebra.norm_le_norm_of_nonneg_of_le
    (a := ofUltraweak x) (b := p) hx.1 hx.2).trans (IsStarProjection.norm_le p hp)

omit [CompleteSpace P] in
private lemma mem_Icc_zero_projection_iff {x : σ(M, P)} :
    x ∈ Icc (0 : σ(M, P)) (toUltraweak ℂ P p) ↔
      x ∈ ultraweakRange (P := P) hp ∧ 0 ≤ x ∧ ‖ofUltraweak x‖ ≤ 1 := by
  rw [mem_ultraweakRange_iff (P := P) hp]
  constructor
  · intro hx
    have hpx := hp.conjugate_of_nonneg_of_le (a := ofUltraweak x) hx.1 hx.2
    have hmem : ofUltraweak x ∈ Subsemigroup.corner p := ⟨ofUltraweak x, hpx⟩
    exact ⟨(Subsemigroup.mem_corner_iff hp.isIdempotentElem).mp hmem, hx.1,
      (CStarAlgebra.norm_le_norm_of_nonneg_of_le
        (a := ofUltraweak x) (b := p) hx.1 hx.2).trans (IsStarProjection.norm_le p hp)⟩
  · rintro ⟨hx, hx0, hxnorm⟩
    refine ⟨hx0, ?_⟩
    have hx1 : ofUltraweak x ≤ 1 :=
      (CStarAlgebra.norm_le_one_iff_of_nonneg (ofUltraweak x) hx0).mp hxnorm
    calc
      ofUltraweak x = p * ofUltraweak x * p := by rw [hx.1, hx.2]
      _ ≤ p * 1 * p := by
        simpa [hp.isSelfAdjoint.star_eq] using star_right_conjugate_le_conjugate hx1 p
      _ = p := by simp [hp.isIdempotentElem.eq]

private lemma isCompact_ultraweakRange_inter_unitClosedBall :
    IsCompact ((ultraweakRange (P := P) hp : Set σ(M, P)) ∩
      ofUltraweak ⁻¹' Metric.closedBall (0 : M) 1) := by
  let K : Set σ(M, P) := Icc 0 (toUltraweak ℂ P p)
  have hK : IsCompact K := isCompact_Icc_zero_projection hp
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let f : (Fin 4 → K) → σ(M, P) := fun x ↦
    ∑ i : Fin 4, Complex.I ^ (i : ℕ) • (x i : σ(M, P))
  have hf : Continuous f := by
    apply continuous_finsetSum Finset.univ
    intro i _
    exact (continuous_subtype_val.comp (continuous_apply i)).const_smul _
  let B : Set σ(M, P) := ofUltraweak ⁻¹' Metric.closedBall (0 : M) 1
  have hB : IsClosed B := Ultraweak.isClosed_closedBall ℂ P (0 : M) 1
  have hpre : IsCompact (f ⁻¹' B) := (hB.preimage hf).isCompact
  suffices f '' (f ⁻¹' B) = (ultraweakRange (P := P) hp : Set σ(M, P)) ∩ B by
    rw [← this]
    exact hpre.image hf
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨?_, hz⟩
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ <|
      (mem_Icc_zero_projection_iff (P := P) hp).mp (z i).property |>.1
  · rintro ⟨⟨x₀, hx₀⟩, hxB⟩
    have hx₀M : (x₀ : M) = ofUltraweak x := congr_arg ofUltraweak hx₀
    have hx₀norm : ‖x₀‖ ≤ 1 := by
      rw [← norm_coe hp, hx₀M]
      simpa [B, Metric.mem_closedBall, dist_zero_right] using hxB
    obtain ⟨a, ha0, hanorm, ha⟩ := CStarAlgebra.exists_sum_four_nonneg x₀
    let z : Fin 4 → K := fun i ↦ ⟨ultraweakInclusionₗ (P := P) hp (a i), by
      apply (mem_Icc_zero_projection_iff (P := P) hp).mpr
      refine ⟨⟨a i, rfl⟩, ?_, ?_⟩
      · exact ha0 i
      · simpa using (hanorm i).trans hx₀norm⟩
    have hzx : f z = x := by
      rw [← hx₀]
      apply (Ultraweak.linearEquiv ℂ M P).injective
      calc
        Ultraweak.linearEquiv ℂ M P (f z) =
            ∑ i : Fin 4, Complex.I ^ (i : ℕ) • (a i : M) := by simp [f, z]
        _ = (x₀ : M) := by
          simpa only [map_sum, map_smul, inclusionL_apply] using
            congr_arg (inclusionL hp) ha.symm
        _ = Ultraweak.linearEquiv ℂ M P (ultraweakInclusionₗ (P := P) hp x₀) := rfl
    refine ⟨z, ?_, hzx⟩
    change f z ∈ B
    rwa [hzx]

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace P] in
include hp in
private lemma mem_range_ultraweakMulLeftₗ_of_mem_upperOffDiagonalUnit
    {x : σ(M, P)} (hx : x ∈ upperOffDiagonalUnit (P := P) (p := p)) :
    x ∈ LinearMap.range (Ultraweak.mulLeftₗ (𝕜 := ℂ) (P := P) p) := by
  rw [hp.mem_range_ultraweakMulLeftₗ_iff]
  obtain ⟨a, -, -, rfl⟩ := hx
  simp [← mul_assoc, hp.isIdempotentElem.eq]

include hp in
private lemma isCompact_range_ultraweakMulLeftₗ_inter_unitClosedBall :
    IsCompact ((LinearMap.range (Ultraweak.mulLeftₗ (𝕜 := ℂ) (P := P) p) : Set σ(M, P)) ∩
      ofUltraweak ⁻¹' Metric.closedBall (0 : M) 1) := by
  let B : Set σ(M, P) := ofUltraweak ⁻¹' Metric.closedBall (0 : M) 1
  let Q : Set σ(M, P) :=
    (ultraweakRange (P := P) hp : Set σ(M, P)) ∩ B
  let U : Set σ(M, P) := upperOffDiagonalUnit (P := P) (p := p)
  rw [show (LinearMap.range (Ultraweak.mulLeftₗ (𝕜 := ℂ) (P := P) p) : Set σ(M, P)) ∩ B =
      (Q + U) ∩ B by
    ext x
    constructor
    · rintro ⟨hx, hxB⟩
      have hpx := hp.mem_range_ultraweakMulLeftₗ_iff.mp hx
      have hx_norm : ‖ofUltraweak x‖ ≤ 1 := by
        simpa [B, Metric.mem_closedBall, dist_zero_right] using hxB
      let q := toUltraweak ℂ P (p * ofUltraweak x * p)
      let u := toUltraweak ℂ P (p * ofUltraweak x * (1 - p))
      have hq : q ∈ Q := ⟨⟨cutdownL hp (ofUltraweak x), rfl⟩, by
        simp only [B, q, mem_preimage, Metric.mem_closedBall, dist_zero_right,
          ofUltraweak_toUltraweak]
        calc
          ‖p * ofUltraweak x * p‖ = ‖cutdownL hp (ofUltraweak x)‖ := by
            rw [← norm_coe hp]
            rfl
          _ ≤ 1 := (norm_cutdownL_le hp (ofUltraweak x)).trans hx_norm⟩
      have hu : u ∈ U := upperOffDiagonal_mem_upperOffDiagonalUnit (P := P) hp hx_norm
      refine ⟨?_, hxB⟩
      rw [← show q + u = x by
        rw [← ofUltraweak_inj]
        simp only [q, u, ofUltraweak_add, ofUltraweak_toUltraweak]
        calc
          p * ofUltraweak x * p + p * ofUltraweak x * (1 - p) =
              p * ofUltraweak x := by noncomm_ring
          _ = ofUltraweak x := hpx]
      exact Set.add_mem_add hq hu
    · rintro ⟨hQU, hxB⟩
      obtain ⟨q, hq, u, hu, rfl⟩ := Set.mem_add.mp hQU
      exact ⟨(LinearMap.range (Ultraweak.mulLeftₗ (𝕜 := ℂ) (P := P) p)).add_mem
        (hp.mem_range_ultraweakMulLeftₗ_iff.mpr <|
          (mem_ultraweakRange_iff (P := P) hp).mp hq.1 |>.1)
        (mem_range_ultraweakMulLeftₗ_of_mem_upperOffDiagonalUnit (P := P) hp hu), hxB⟩]
  exact ((isCompact_ultraweakRange_inter_unitClosedBall (P := P) hp).add
    (isCompact_upperOffDiagonalUnit (P := P) hp)).inter_right <|
      Ultraweak.isClosed_closedBall ℂ P (0 : M) 1

set_option backward.isDefEq.respectTransparency false in
/-- A projection corner is closed in the ambient ultraweak topology. -/
theorem isClosed_ultraweakRange : IsClosed (ultraweakRange (P := P) hp : Set σ(M, P)) := by
  apply Ultraweak.krein_smulian_of_submodule <|
    (ultraweakRange (P := P) hp).restrictScalars NNReal
  simpa using (isCompact_ultraweakRange_inter_unitClosedBall (P := P) hp).isClosed

/-- The quotient predual induced on a projection corner by an explicitly specified ambient
predual. -/
@[implicit_reducible]
noncomputable def inducedPredual :
    Predual ℂ hp.Corner
      (P ⧸ Ultraweak.preannihilator (P := P) (rangeSubmodule hp)) := by
  let hN : IsClosed
      (Ultraweak.ofSubmodule (P := P) (rangeSubmodule hp) : Set σ(M, P)) := by
    rw [← ultraweakRange_eq_ofSubmodule (P := P) hp]
    exact isClosed_ultraweakRange (P := P) hp
  exact ⟨(toRangeSubmoduleₗᵢ hp).trans
    (Ultraweak.closedSubmoduleEquivDual (P := P) (rangeSubmodule hp) hN)⟩

/-- A projection corner in a dual C-star algebra is a W-star algebra. -/
theorem wStarAlgebra {P' : Type u} [NormedAddCommGroup P'] [NormedSpace ℂ P']
    [CompleteSpace P'] [Predual ℂ M P'] : WStarAlgebra hp.Corner := by
  apply WStarAlgebra.of_isClosed_submodule hp.Corner P' M (rangeSubmodule hp)
    (toRangeSubmoduleₗᵢ hp)
  rw [← ultraweakRange_eq_ofSubmodule (P := P') hp]
  exact isClosed_ultraweakRange (P := P') hp

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace P] in
private lemma exists_peirce_decomposition_of_mem_ker_ultraweakCutdownₗ
    {a : σ(M, P)} (ha : a ∈ LinearMap.ker (ultraweakCutdownₗ (P := P) hp))
    (ha_norm : ‖ofUltraweak a‖ ≤ 1) :
    ∃ u ∈ upperOffDiagonalUnit (P := P) (p := p),
      ∃ v ∈ upperOffDiagonalUnit (P := P) (p := 1 - p),
      ∃ q ∈ (ultraweakRange (P := P) hp.one_sub : Set σ(M, P)) ∩
        ofUltraweak ⁻¹' Metric.closedBall (0 : M) 1, u + v + q = a := by
  let b := p * ofUltraweak a * (1 - p)
  let c := (1 - p) * ofUltraweak a * p
  let d := (1 - p) * ofUltraweak a * (1 - p)
  refine ⟨toUltraweak ℂ P b, by
      simpa [b] using upperOffDiagonal_mem_upperOffDiagonalUnit (P := P) hp ha_norm,
    toUltraweak ℂ P c, by
      simpa [c] using upperOffDiagonal_mem_upperOffDiagonalUnit (P := P) hp.one_sub ha_norm,
    toUltraweak ℂ P d, ⟨⟨cutdownL hp.one_sub (ofUltraweak a), rfl⟩, ?_⟩, ?_⟩
  · simp only [mem_preimage, Metric.mem_closedBall, dist_zero_right]
    calc
      ‖d‖ = ‖cutdownL hp.one_sub (ofUltraweak a)‖ := by
        rw [← norm_coe hp.one_sub]
        rfl
      _ ≤ ‖ofUltraweak a‖ := norm_cutdownL_le hp.one_sub _
      _ ≤ 1 := ha_norm
  · rw [← ofUltraweak_inj]
    change b + c + d = ofUltraweak a
    have hpa := (mem_ker_ultraweakCutdownₗ_iff (P := P) hp).mp ha
    calc
      b + c + d = p * ofUltraweak a * p + b + c + d := by rw [hpa]; simp
      _ = ofUltraweak a := by
        simpa [b, c, d] using (peirce_decomposition p (ofUltraweak a)).symm

private lemma isCompact_ker_ultraweakCutdownₗ_inter_unitClosedBall :
    IsCompact ((LinearMap.ker (ultraweakCutdownₗ (P := P) hp) : Set σ(M, P)) ∩
      ofUltraweak ⁻¹' Metric.closedBall (0 : M) 1) := by
  let B : Set σ(M, P) := ofUltraweak ⁻¹' Metric.closedBall (0 : M) 1
  let U : Set σ(M, P) := closure (upperOffDiagonalUnit (P := P) (p := p))
  let V : Set σ(M, P) := closure (upperOffDiagonalUnit (P := P) (p := 1 - p))
  let Q : Set σ(M, P) :=
    (ultraweakRange (P := P) hp.one_sub : Set σ(M, P)) ∩ B
  rw [show (LinearMap.ker (ultraweakCutdownₗ (P := P) hp) : Set σ(M, P)) ∩ B =
      (U + V + Q) ∩ B by
    ext a
    constructor
    · rintro ⟨ha, haB⟩
      obtain ⟨u, hu, v, hv, q, hq, rfl⟩ :=
        exists_peirce_decomposition_of_mem_ker_ultraweakCutdownₗ (P := P) hp ha <| by
          simpa [B, Metric.mem_closedBall, dist_zero_right] using haB
      exact ⟨Set.add_mem_add (Set.add_mem_add (subset_closure hu) (subset_closure hv)) hq, haB⟩
    · rintro ⟨ha, haB⟩
      obtain ⟨uv, ⟨u, hu, v, hv, rfl⟩, q, hq, rfl⟩ := Set.mem_add.mp ha
      exact ⟨(LinearMap.ker (ultraweakCutdownₗ (P := P) hp)).add_mem
        ((LinearMap.ker (ultraweakCutdownₗ (P := P) hp)).add_mem
          (mem_ker_ultraweakCutdownₗ_of_mem_closure_upperOffDiagonalUnit
            (P := P) hp hu)
          (mem_ker_ultraweakCutdownₗ_of_mem_closure_lowerOffDiagonalUnit
            (P := P) hp hv))
        (mem_ker_ultraweakCutdownₗ_of_mem_ultraweakRange_one_sub
          (P := P) hp hq.1), haB⟩]
  exact ((isCompact_closure_upperOffDiagonalUnit (P := P) hp).add
    (isCompact_closure_upperOffDiagonalUnit (P := P) hp.one_sub) |>.add
      (isCompact_ultraweakRange_inter_unitClosedBall (P := P) hp.one_sub)).inter_right <|
        Ultraweak.isClosed_closedBall ℂ P (0 : M) 1

set_option backward.isDefEq.respectTransparency false in
/-- The kernel of projection cutdown is closed in the ambient ultraweak topology. -/
theorem isClosed_ker_ultraweakCutdownₗ :
    IsClosed (LinearMap.ker (ultraweakCutdownₗ (P := P) hp) : Set σ(M, P)) := by
  apply Ultraweak.krein_smulian_of_submodule <|
    (LinearMap.ker (ultraweakCutdownₗ (P := P) hp)).restrictScalars NNReal
  simpa using (isCompact_ker_ultraweakCutdownₗ_inter_unitClosedBall (P := P) hp).isClosed

/-- Projection cutdown is ultraweakly continuous. -/
theorem continuous_ultraweakCutdownₗ :
    Continuous (ultraweakCutdownₗ (P := P) hp) := by
  apply Ultraweak.continuous_of_isClosed_range_ker_of_idempotent
  · exact ultraweakCutdownₗ_idempotent (P := P) hp
  · rw [range_ultraweakCutdownₗ (P := P) hp]
    exact isClosed_ultraweakRange (P := P) hp
  · exact isClosed_ker_ultraweakCutdownₗ (P := P) hp
  · intro x hx
    simp only [mem_preimage, Metric.mem_closedBall, dist_zero_right] at hx ⊢
    exact (norm_ultraweakCutdownₗ_le (P := P) hp x).trans hx

set_option backward.isDefEq.respectTransparency false in
include hp in
/-- The range of left multiplication by a projection is ultraweakly closed. -/
theorem _root_.IsStarProjection.isClosed_range_ultraweakMulLeftₗ :
    IsClosed (LinearMap.range (Ultraweak.mulLeftₗ (𝕜 := ℂ) (P := P) p) : Set σ(M, P)) := by
  apply Ultraweak.krein_smulian_of_submodule <|
    (LinearMap.range (Ultraweak.mulLeftₗ (𝕜 := ℂ) (P := P) p)).restrictScalars NNReal
  simpa using
    (isCompact_range_ultraweakMulLeftₗ_inter_unitClosedBall (P := P) hp).isClosed

include hp in
/-- The kernel of left multiplication by a projection is ultraweakly closed. -/
theorem _root_.IsStarProjection.isClosed_ker_ultraweakMulLeftₗ :
    IsClosed (LinearMap.ker (Ultraweak.mulLeftₗ (𝕜 := ℂ) (P := P) p) : Set σ(M, P)) := by
  rw [← hp.range_ultraweakMulLeftₗ_one_sub]
  exact hp.one_sub.isClosed_range_ultraweakMulLeftₗ (P := P)

include hp in
/-- Left multiplication by a projection is ultraweakly continuous. -/
theorem _root_.IsStarProjection.continuous_ultraweakMulLeftₗ :
    Continuous (Ultraweak.mulLeftₗ (𝕜 := ℂ) (P := P) p) := by
  apply Ultraweak.continuous_of_isClosed_range_ker_of_idempotent
  · exact hp.ultraweakMulLeftₗ_idempotent (P := P)
  · exact hp.isClosed_range_ultraweakMulLeftₗ (P := P)
  · exact hp.isClosed_ker_ultraweakMulLeftₗ (P := P)
  · intro x hx
    simp only [mem_preimage, Metric.mem_closedBall, dist_zero_right] at hx ⊢
    exact (hp.norm_ultraweakMulLeftₗ_le (P := P) x).trans hx

include hp in
/-- Right multiplication by a projection is ultraweakly continuous. -/
theorem _root_.IsStarProjection.continuous_ultraweakMulRightₗ :
    Continuous (Ultraweak.mulRightₗ (𝕜 := ℂ) (P := P) p) := by
  rw [show (Ultraweak.mulRightₗ (𝕜 := ℂ) (P := P) p : σ(M, P) → σ(M, P)) =
      fun x ↦ star (Ultraweak.mulLeftₗ (𝕜 := ℂ) (P := P) p (star x)) by
    funext x
    rw [← ofUltraweak_inj]
    simp [star_mul, hp.isSelfAdjoint.star_eq]]
  exact continuous_star.comp (hp.continuous_ultraweakMulLeftₗ (P := P).comp continuous_star)

/-- The ultraweakly continuous projection from the ambient algebra onto a projection corner. -/
noncomputable def ultraweakCutdownL : σ(M, P) →L[ℂ] σ(M, P) :=
  ⟨ultraweakCutdownₗ (P := P) hp, continuous_ultraweakCutdownₗ (P := P) hp⟩

@[simp] lemma ultraweakCutdownL_apply (x : σ(M, P)) :
    ultraweakCutdownL (P := P) hp x = toUltraweak ℂ P (p * ofUltraweak x * p) := rfl

/-- The positive ultraweakly continuous projection cutdown on the ambient algebra. -/
noncomputable def ultraweakCutdownP : σ(M, P) →P[ℂ] σ(M, P) where
  toFun := ultraweakCutdownL (P := P) hp
  map_add' := map_add (ultraweakCutdownL (P := P) hp)
  map_smul' := map_smul (ultraweakCutdownL (P := P) hp)
  monotone' x y h := by
    change toUltraweak ℂ P (p * ofUltraweak x * p) ≤
      toUltraweak ℂ P (p * ofUltraweak y * p)
    apply Ultraweak.monotone_toUltraweak
    exact hp.isSelfAdjoint.conjugate_le_conjugate (Ultraweak.monotone_ofUltraweak h)
  cont := (ultraweakCutdownL (P := P) hp).continuous

@[simp]
lemma ultraweakCutdownP_apply (x : σ(M, P)) :
    ultraweakCutdownP (P := P) hp x =
      toUltraweak ℂ P (p * ofUltraweak x * p) := rfl

end IsStarProjection.Corner
