module

public import LeanOA.Mathlib.Analysis.CStarAlgebra.Abs
public import LeanOA.Ultraweak.Support

@[expose] public section

/-!
# Support of the absolute value

This file identifies the support of Mathlib's canonical continuous-functional-calculus absolute
value with the corresponding one-sided support of an element of a von Neumann algebra.
-/

namespace WStarAlgebra

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] [WStarAlgebra M]

/-- The support of the absolute value is the right support of the original element. -/
@[simp]
theorem support_abs (a : M) :
    support ⟨CFC.abs a, (CFC.abs_nonneg a).isSelfAdjoint⟩ = rightSupport a := by
  rw [support, IsSelfAdjoint.leftSupport_eq_rightSupport
    (CFC.abs_nonneg a).isSelfAdjoint]
  apply le_antisymm
  · rw [rightSupport_le_iff]
    have ha : a * (1 - (rightSupport a).1) = 0 := by
      rw [mul_sub, mul_one, mul_rightSupport, sub_self]
    have habs := (CFC.abs_mul_eq_zero_iff a (1 - (rightSupport a).1)).2 ha
    rw [mul_sub, mul_one] at habs
    exact (sub_eq_zero.mp habs).symm
  · rw [rightSupport_le_iff]
    have habs : CFC.abs a * (1 - (rightSupport (CFC.abs a)).1) = 0 := by
      rw [mul_sub, mul_one, mul_rightSupport, sub_self]
    have ha := (CFC.abs_mul_eq_zero_iff a (1 - (rightSupport (CFC.abs a)).1)).1 habs
    rw [mul_sub, mul_one] at ha
    exact (sub_eq_zero.mp ha).symm

/-- The support of the absolute value of the adjoint is the left support of the original
element. -/
theorem support_abs_star (a : M) :
    support ⟨CFC.abs (star a), (CFC.abs_nonneg (star a)).isSelfAdjoint⟩ = leftSupport a := by
  rw [support_abs, rightSupport_star]

end WStarAlgebra
