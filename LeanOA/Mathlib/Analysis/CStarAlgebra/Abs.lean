module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs

@[expose] public section

/-!
# Absolute-value identities for non-unital continuous functional calculus

This file records one-sided annihilator equivalences and a modulus-square factorization identity
for Mathlib's canonical continuous-functional-calculus absolute value.
-/

namespace CFC

section Annihilators

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

end Annihilators

section ModulusSquare

variable {A : Type*} [NonUnitalRing A] [StarRing A] [TopologicalSpace A]
  [Module ℝ A] [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]
  [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A]
  [IsTopologicalRing A] [T2Space A]

/-- If `a = u |a|`, conjugating the modulus square by `u` recovers `a a*`. -/
lemma mul_star_eq_of_eq_mul_abs {a u : A} (h : a = u * abs a) :
    a * star a = u * (star a * a) * star u := by
  calc
    a * star a = (u * abs a) * star (u * abs a) := by rw [← h]
    _ = u * (abs a * abs a) * star u := by
      rw [star_mul, (abs_nonneg a).star_eq]
      noncomm_ring
    _ = u * (star a * a) * star u := by rw [abs_mul_abs]

end ModulusSquare

end CFC
