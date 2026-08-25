module

public import LeanOA.PositiveContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
public import Mathlib.Order.ScottContinuity

@[expose] public section

namespace PositiveLinearMap

section Normality

variable {R A B : Type*} [Semiring R]
  [AddCommMonoid A] [PartialOrder A] [Module R A] [Mul A] [Star A]
  [AddCommMonoid B] [PartialOrder B] [Module R B]

/-- A positive linear map is normal on projections if it preserves least upper bounds of
nonempty directed families of star projections.

This order-theoretic predicate deliberately has no topological or C-star-algebra assumptions.
Analytic characterizations of normality should be stated separately, with any chosen predual
kept explicit. -/
def IsNormalOnProjections (f : A →ₚ[R] B) : Prop :=
  ScottContinuous fun p : {p : A // IsStarProjection p} ↦ f p.1

end Normality

variable {A₁ A₂ : Type*} [NonUnitalCStarAlgebra A₁] [NonUnitalCStarAlgebra A₂] [PartialOrder A₁]
  [StarOrderedRing A₁] [PartialOrder A₂] [StarOrderedRing A₂] (f : A₁ →ₚ[ℂ] A₂)

/-- Lift a positive linear map between C⋆-algebras to a positive continuous linear map. -/
def toPositiveContinuousLinearMap : A₁ →P[ℂ] A₂ where
  toPositiveLinearMap := f
  cont := by dsimp; fun_prop

@[simp] theorem toPositiveContinuousLinearMap_apply (x : A₁) :
    f.toPositiveContinuousLinearMap x = f x := rfl
@[simp] theorem toPositiveContinuousLinearMap_zero :
    (0 : A₁ →ₚ[ℂ] A₂).toPositiveContinuousLinearMap = 0 := rfl
@[simp] lemma toPositiveContinuousLinearMap_id :
    (PositiveLinearMap.id ℂ A₁).toPositiveContinuousLinearMap = .id ℂ A₁ := rfl

-- maybe remove the following?
/-- Lift a positive linear map between C⋆-algebras to a continuous linear map. -/
abbrev toContinuousLinearMap : A₁ →L[ℂ] A₂ := f.toPositiveContinuousLinearMap.toContinuousLinearMap

theorem toContinuousLinearMap_apply (x : A₁) : f.toContinuousLinearMap x = f x := rfl
@[simp] theorem toContinuousLinearMap_zero : (0 : A₁ →ₚ[ℂ] A₂).toContinuousLinearMap = 0 := rfl
@[simp] theorem toLinearMap_toContinuousLinearMap :
    f.toContinuousLinearMap.toLinearMap = f.toLinearMap := rfl
@[simp] lemma toContinuousLinearMap_id :
    (PositiveLinearMap.id ℂ A₁).toContinuousLinearMap = .id ℂ A₁ := rfl

end PositiveLinearMap
