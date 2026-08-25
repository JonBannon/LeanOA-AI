module

public import Mathlib.Analysis.CStarAlgebra.GelfandDuality
public import Mathlib.Tactic.NoncommRing

@[expose] public section

namespace CStarRing

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- An off-diagonal element of a C⋆-algebra has the same norm as its selfadjoint
dilation. -/
lemma norm_add_star_of_mul_self_eq_zero {a : A} (ha : a * a = 0) :
    ‖a + star a‖ = ‖a‖ := by
  have hstar : star a * star a = 0 := by simpa [star_mul] using congr_arg star ha
  have horth : (a * star a) * (star a * a) = 0 := by
    rw [mul_assoc, ← mul_assoc (star a), hstar]
    simp
  have hsq : ‖a + star a‖ ^ 2 = ‖a‖ ^ 2 := by
    calc
      ‖a + star a‖ ^ 2 = ‖star (a + star a) * (a + star a)‖ := by
        simpa [pow_two] using (CStarRing.norm_star_mul_self (x := a + star a)).symm
      _ = ‖a * star a + star a * a‖ := by
        congr 1
        simp [star_add, add_mul, mul_add, ha, hstar, add_comm]
      _ = max ‖a * star a‖ ‖star a * a‖ :=
        (IsSelfAdjoint.mul_star_self a).norm_add_eq_max
          (IsSelfAdjoint.star_mul_self a) horth
      _ = ‖a‖ ^ 2 := by simp [pow_two, CStarRing.norm_self_mul_star,
        CStarRing.norm_star_mul_self]
  nlinarith [norm_nonneg a, norm_nonneg (a + star a)]

/-- Orthogonal C⋆-algebra elements satisfy the Pythagorean norm inequality. -/
lemma norm_add_le_sqrt_of_mul_star_eq_zero {a b : A} (hab : a * star b = 0) :
    ‖a + b‖ ≤ √(‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  have hba : b * star a = 0 := by
    simpa only [star_mul, star_star, star_zero] using congr_arg star hab
  rw [Real.le_sqrt (norm_nonneg _) (by positivity), pow_two,
    ← CStarRing.norm_self_mul_star]
  calc
    ‖(a + b) * star (a + b)‖ = ‖a * star a + b * star b‖ := by
      simp [star_add, mul_add, add_mul, hab, hba]
    _ ≤ ‖a * star a‖ + ‖b * star b‖ := norm_add_le ..
    _ = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
      simp [pow_two, CStarRing.norm_self_mul_star]

/-- Elements orthogonal on both sides have max norm under addition. -/
lemma norm_add_eq_max_of_mul_star_eq_zero_of_star_mul_eq_zero {a b : A}
    (hab : a * star b = 0) (h'ab : star a * b = 0) :
    ‖a + b‖ = max ‖a‖ ‖b‖ := by
  have h'ba : star b * a = 0 := by
    simpa only [star_mul, star_star, star_zero] using congr_arg star h'ab
  have horth : (star a * a) * (star b * b) = 0 := by
    rw [mul_assoc, ← mul_assoc a, hab]
    simp
  have hsq : ‖a + b‖ ^ 2 = max ‖a‖ ‖b‖ ^ 2 := by
    calc
      ‖a + b‖ ^ 2 = ‖star (a + b) * (a + b)‖ := by
        simpa [pow_two] using (CStarRing.norm_star_mul_self (x := a + b)).symm
      _ = ‖star a * a + star b * b‖ := by
        congr 1
        simp [star_add, add_mul, mul_add, h'ab, h'ba]
      _ = max ‖star a * a‖ ‖star b * b‖ :=
        (IsSelfAdjoint.star_mul_self a).norm_add_eq_max
          (IsSelfAdjoint.star_mul_self b) horth
      _ = max ‖a‖ ‖b‖ ^ 2 := by
        simp only [CStarRing.norm_star_mul_self]
        rcases le_total ‖a‖ ‖b‖ with hab | hba
        · rw [max_eq_right hab, max_eq_right (mul_self_le_mul_self (norm_nonneg a) hab),
            pow_two]
        · rw [max_eq_left hba, max_eq_left (mul_self_le_mul_self (norm_nonneg b) hba),
            pow_two]
  nlinarith [norm_nonneg (a + b), norm_nonneg a, norm_nonneg b,
    le_max_left ‖a‖ ‖b‖, le_max_right ‖a‖ ‖b‖]

end CStarRing

/-- A self-adjoint right identity on `star x * x` is already a right identity on `x`. -/
lemma IsSelfAdjoint.mul_eq_self_of_star_mul_self_mul_eq {A : Type*}
    [NonUnitalCStarAlgebra A] {p x : A} (hp : IsSelfAdjoint p)
    (h : (star x * x) * p = star x * x) : x * p = x := by
  have h' : p * (star x * x) = star x * x := by
    simpa only [star_mul, star_star, hp.star_eq] using congr_arg star h
  symm
  rw [← sub_eq_zero, ← CStarRing.star_mul_self_eq_zero_iff (x - x * p)]
  calc
    star (x - x * p) * (x - x * p) =
        star x * x - (star x * x) * p - p * (star x * x) +
          p * (star x * x) * p := by
      rw [star_sub, star_mul, hp.star_eq]
      noncomm_ring
    _ = 0 := by rw [h, h', h]; simp

namespace StarAlgHom

/-- A complex star-algebra homomorphism maps the real span of star projections into the real span
of star projections. -/
lemma mapsTo_span_isStarProjection {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    (f : A →⋆ₐ[ℂ] B) :
    Set.MapsTo f (Submodule.span ℝ {p : A | IsStarProjection p})
      (Submodule.span ℝ {p : B | IsStarProjection p}) :=
  Set.image_subset_iff.mp <|
    (Submodule.image_span_subset (f.restrictScalars ℝ).toLinearMap
      {p : A | IsStarProjection p} (Submodule.span ℝ {p : B | IsStarProjection p})).2
        fun _ hp ↦ Submodule.mem_span_of_mem (hp.map f)

end StarAlgHom
