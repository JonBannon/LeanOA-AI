module

public import LeanOA.CStarAlgebra.Extreme
public import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
public import Mathlib.Tactic.NoncommRing

@[expose] public section

open Metric Set
open scoped NNReal Ring

namespace CStarAlgebra

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The positive resolvent `R_a = (1 + a⋆a)⁻¹` used in Sakai's density argument. -/
noncomputable def kaplanskyResolvent (a : A) : A := (1 + star a * a)⁻¹ʳ

/-- Sakai's contraction transform `a ↦ 2a(1 + a⋆a)⁻¹`. -/
noncomputable def kaplanskyTransform (a : A) : A :=
  (2 : ℕ) • (a * kaplanskyResolvent a)

/-- The positive element occurring in the denominator of `kaplanskyTransform` is invertible. -/
lemma isUnit_one_add_star_mul_self (a : A) : IsUnit (1 + star a * a) := by
  apply CStarAlgebra.isUnit_of_le 1
  simpa only [le_add_iff_nonneg_right] using star_mul_self_nonneg a

@[simp]
lemma one_add_star_mul_self_mul_kaplanskyResolvent (a : A) :
    (1 + star a * a) * kaplanskyResolvent a = 1 := by
  exact Ring.mul_inverse_cancel _ (isUnit_one_add_star_mul_self a)

@[simp]
lemma kaplanskyResolvent_mul_one_add_star_mul_self (a : A) :
    kaplanskyResolvent a * (1 + star a * a) = 1 := by
  exact Ring.inverse_mul_cancel _ (isUnit_one_add_star_mul_self a)

lemma kaplanskyResolvent_nonneg (a : A) : 0 ≤ kaplanskyResolvent a := by
  have h : IsStrictlyPositive (1 + star a * a) :=
    ⟨zero_le_one.trans (by
      simpa only [le_add_iff_nonneg_right] using star_mul_self_nonneg a),
      isUnit_one_add_star_mul_self a⟩
  exact h.ringInverse.nonneg

lemma kaplanskyResolvent_le_one (a : A) : kaplanskyResolvent a ≤ 1 := by
  change (1 + star a * a)⁻¹ʳ ≤ 1
  simpa using CStarAlgebra.ringInverse_le_ringInverse
    (a := (1 : A)) (b := 1 + star a * a)
    (by simpa only [le_add_iff_nonneg_right] using star_mul_self_nonneg a)

/-- Sakai's positive resolvents are contractions. -/
lemma norm_kaplanskyResolvent_le_one (a : A) : ‖kaplanskyResolvent a‖ ≤ 1 := by
  rw [CStarAlgebra.norm_le_one_iff_of_nonneg _ (kaplanskyResolvent_nonneg a)]
  exact kaplanskyResolvent_le_one a

omit [PartialOrder A] [StarOrderedRing A] in
private lemma inverse_one_add_star_mul_self_isSelfAdjoint (a : A) :
    IsSelfAdjoint (1 + star a * a)⁻¹ʳ :=
  (IsSelfAdjoint.one A |>.add (IsSelfAdjoint.star_mul_self a)).ringInverse

omit [PartialOrder A] [StarOrderedRing A] in
private lemma star_mul_self_ringInverse_identity (b r : A) (hr : IsSelfAdjoint r)
    (hmul : (1 + b) * r = 1) (hcomm : b * r = r * b) :
    1 - (4 : ℕ) • (r * b * r) = star ((1 - b) * r) * ((1 - b) * r) := by
  have hbr : b * r = 1 - r := by
    calc
      b * r = (1 + b) * r - r := by noncomm_ring
      _ = 1 - r := by rw [hmul]
  have hrb : r * b = 1 - r := hcomm.symm.trans hbr
  have hone_sub : (1 - b) * r = (2 : ℕ) • r - 1 := by
    rw [sub_mul, one_mul, hbr]
    module
  rw [hone_sub, star_sub, star_smul, hr.star_eq, star_one]
  simp only [star_ofNat]
  noncomm_ring [hrb]

private lemma star_mul_self_ringInverse_identity' (a : A) :
    let b := star a * a
    let r := (1 + b)⁻¹ʳ
    1 - (4 : ℕ) • (r * b * r) = star ((1 - b) * r) * ((1 - b) * r) := by
  dsimp only
  have hu : IsUnit (1 + star a * a) := isUnit_one_add_star_mul_self a
  have hmul : (1 + star a * a) * (1 + star a * a)⁻¹ʳ = 1 := Ring.mul_inverse_cancel _ hu
  have hinv_mul : (1 + star a * a)⁻¹ʳ * (1 + star a * a) = 1 :=
    Ring.inverse_mul_cancel _ hu
  have hcomm : (star a * a) * (1 + star a * a)⁻¹ʳ =
      (1 + star a * a)⁻¹ʳ * (star a * a) := by
    calc
      (star a * a) * (1 + star a * a)⁻¹ʳ =
          (1 + star a * a) * (1 + star a * a)⁻¹ʳ -
            (1 + star a * a)⁻¹ʳ := by noncomm_ring
      _ = 1 - (1 + star a * a)⁻¹ʳ := by rw [hmul]
      _ = (1 + star a * a)⁻¹ʳ * (1 + star a * a) -
            (1 + star a * a)⁻¹ʳ := by rw [hinv_mul]
      _ = (1 + star a * a)⁻¹ʳ * (star a * a) := by noncomm_ring
  exact star_mul_self_ringInverse_identity (star a * a) (1 + star a * a)⁻¹ʳ
    (inverse_one_add_star_mul_self_isSelfAdjoint a) hmul hcomm

/-- Sakai's transform is a contraction. -/
theorem norm_kaplanskyTransform_le_one (a : A) : ‖kaplanskyTransform a‖ ≤ 1 := by
  let b := star a * a
  let r := (1 + b)⁻¹ʳ
  have hr : IsSelfAdjoint r := inverse_one_add_star_mul_self_isSelfAdjoint a
  have hstar_mul :
      star (kaplanskyTransform a) * kaplanskyTransform a = (4 : ℕ) • (r * b * r) := by
    simp only [kaplanskyTransform, kaplanskyResolvent, star_nsmul, star_mul, hr.star_eq, b, r]
    noncomm_ring
  have hnonneg : 0 ≤ star (kaplanskyTransform a) * kaplanskyTransform a :=
    star_mul_self_nonneg _
  have hle : star (kaplanskyTransform a) * kaplanskyTransform a ≤ 1 := by
    rw [hstar_mul, ← sub_nonneg]
    rw [star_mul_self_ringInverse_identity' a]
    exact star_mul_self_nonneg _
  rw [← sq_le_one_iff₀ (norm_nonneg _), sq, ← CStarRing.norm_star_mul_self,
    CStarAlgebra.norm_le_one_iff_of_nonneg _ hnonneg]
  exact hle

/-- The unscaled factor `a(1 + a⋆a)⁻¹` in Sakai's transform has norm at most `1/2`. -/
theorem norm_mul_kaplanskyResolvent_le_half (a : A) :
    ‖a * kaplanskyResolvent a‖ ≤ (1 / 2 : ℝ) := by
  have h := norm_kaplanskyTransform_le_one a
  rw [kaplanskyTransform] at h
  have htwo : (2 : ℕ) • (a * kaplanskyResolvent a) =
      (2 : ℂ) • (a * kaplanskyResolvent a) := by module
  rw [htwo, norm_smul] at h
  norm_num at h ⊢
  linarith

theorem kaplanskyTransform_mem_closedBall (a : A) :
    kaplanskyTransform a ∈ closedBall 0 1 := by
  simpa [mem_closedBall, dist_zero_right] using norm_kaplanskyTransform_le_one a

/-- The non-unital functional-calculus cutoff used by Mathlib's approximate-unit construction is
the complement of the resolvent of `1 + b`. -/
lemma cfcₙ_one_sub_one_add_inv (b : A) (hb : 0 ≤ b := by cfc_tac) :
    cfcₙ (fun x : ℝ≥0 ↦ 1 - (1 + x)⁻¹) b = 1 - (1 + b)⁻¹ʳ := by
  rw [cfcₙ_eq_cfc]
  have hunit : IsUnit (1 + b) := CStarAlgebra.isUnit_of_le 1 <| by
    simpa only [le_add_iff_nonneg_right] using hb
  rw [cfc_tsub _ _ _ (fun x _ ↦ by simp)
      (hg := by fun_prop (disch := intro _ _; positivity)),
    cfc_const_one ℝ≥0 b, cfc_comp' (·⁻¹) (1 + ·) b ?_, cfc_add ..,
    cfc_const_one ℝ≥0 b, cfc_id' ℝ≥0 b]
  · rw [cfc_ringInverse_id (1 + b) hunit]
  · exact continuousOn_id.inv₀
      (Set.forall_mem_image.mpr fun x _ ↦ by dsimp only [id]; positivity)

/-- The Kaplansky transform stays in a norm-closed non-unital star subalgebra.  The proof uses the
same non-unital functional-calculus cutoff as Mathlib's construction of approximate units, so no
identity element is introduced into the subalgebra. -/
theorem kaplanskyTransform_mem_nonUnitalStarSubalgebra
    (S : NonUnitalStarSubalgebra ℂ A) [IsClosed (S : Set A)] {a : A} (ha : a ∈ S) :
    kaplanskyTransform a ∈ S := by
  let b : A := star a * a
  let e : A := cfcₙ (fun x : ℝ≥0 ↦ 1 - (1 + x)⁻¹) b
  have hb_nonneg : 0 ≤ b := star_mul_self_nonneg a
  have hb_mem : b ∈ S := S.mul_mem (StarMemClass.star_mem (s := S) ha) ha
  have he_mem : e ∈ S := by
    dsimp only [e]
    rw [cfcₙ_nnreal_eq_real _ _ hb_nonneg]
    exact cfcₙ_mem _ hb_mem
  have he : e = 1 - (1 + b)⁻¹ʳ := cfcₙ_one_sub_one_add_inv b hb_nonneg
  rw [kaplanskyTransform, kaplanskyResolvent]
  have hrewrite : a * (1 + star a * a)⁻¹ʳ = a - a * e := by
    rw [he]
    dsimp only [b]
    noncomm_ring
  rw [hrewrite]
  exact S.nsmul_mem (S.sub_mem ha (S.mul_mem ha he_mem)) 2

/-- Sakai's contraction transform fixes every extreme point of the closed unit ball. -/
theorem kaplanskyTransform_eq_self_of_mem_extremePoints_unitClosedBall {a : A}
    (ha : a ∈ extremePoints ℝ (closedBall 0 1)) : kaplanskyTransform a = a := by
  let p : A := star a * a
  have hp : IsStarProjection p :=
    isStarProjection_star_mul_self_of_mem_extremePoints_unitClosedBall ha
  have hp_idem : p * p = p := hp.isIdempotentElem.eq
  let q : A := 1 - (1 / 2 : ℂ) • p
  have hmul : (1 + p) * q = 1 := by
    dsimp only [q]
    rw [mul_sub, mul_one, add_mul, one_mul, mul_smul_comm, hp_idem]
    module
  have hu : IsUnit (1 + p) := by
    dsimp only [p]
    exact isUnit_one_add_star_mul_self a
  have hinv : (1 + p)⁻¹ʳ = q := by
    calc
      (1 + p)⁻¹ʳ = (1 + p)⁻¹ʳ * 1 := by rw [mul_one]
      _ = (1 + p)⁻¹ʳ * ((1 + p) * q) := by rw [hmul]
      _ = q := by rw [← mul_assoc, Ring.inverse_mul_cancel _ hu, one_mul]
  have hap : a * p = a := by
    dsimp only [p]
    simpa only [mul_assoc] using
      star_self_conjugate_eq_self_of_mem_extremePoints_unitClosedBall ha
  rw [kaplanskyTransform, kaplanskyResolvent]
  change (2 : ℕ) • (a * (1 + p)⁻¹ʳ) = a
  rw [hinv]
  dsimp only [q]
  rw [mul_sub, mul_one, mul_smul_comm, hap]
  module


end CStarAlgebra
