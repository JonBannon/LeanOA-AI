module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs

@[expose] public section

/-!
# Absolute-value annihilators in non-unital C-star algebras

This file records the one-sided annihilator equivalences relating an element to Mathlib's
canonical continuous-functional-calculus absolute value.
-/

namespace CFC

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Left multiplication by `CFC.abs a` and by `a` have the same right annihilator. -/
lemma abs_mul_eq_zero_iff (a x : A) : abs a * x = 0 ↔ a * x = 0 := by
  have hsquare : star (abs a * x) * (abs a * x) = star (a * x) * (a * x) := by
    calc
      star (abs a * x) * (abs a * x) = star x * (abs a * abs a) * x := by
        simp only [star_mul, (abs_nonneg a).star_eq, mul_assoc]
      _ = star x * (star a * a) * x := by rw [abs_mul_abs]
      _ = star (a * x) * (a * x) := by simp only [star_mul, mul_assoc]
  rw [← CStarRing.star_mul_self_eq_zero_iff (abs a * x),
    ← CStarRing.star_mul_self_eq_zero_iff (a * x), hsquare]

/-- Right multiplication by `CFC.abs a` and by `star a` have the same left annihilator. -/
lemma mul_abs_eq_zero_iff (x a : A) : x * abs a = 0 ↔ x * star a = 0 := by
  constructor
  · intro h
    have h' : abs a * star x = 0 := by
      simpa only [star_mul, (abs_nonneg a).star_eq, star_zero] using congr_arg star h
    have : a * star x = 0 := (abs_mul_eq_zero_iff a (star x)).mp h'
    simpa only [star_mul, star_star, star_zero] using congr_arg star this
  · intro h
    have h' : a * star x = 0 := by
      simpa only [star_mul, star_star, star_zero] using congr_arg star h
    have : abs a * star x = 0 := (abs_mul_eq_zero_iff a (star x)).mpr h'
    simpa only [star_mul, star_star, (abs_nonneg a).star_eq, star_zero] using
      congr_arg star this

end CFC
