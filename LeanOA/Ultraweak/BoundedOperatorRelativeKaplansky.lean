module

public import LeanOA.Ultraweak.BoundedOperatorInvariantTestSpace
public import LeanOA.Ultraweak.BoundedOperatorWOTClosure
public import LeanOA.Ultraweak.RelativeKaplanskyDensity

/-!
# Kaplansky density inside WOT closure on `B(H)`

The finite vector-functional core induces Mathlib's WOT.  Combining that identification with
ambient-relative Kaplansky density shows that the unit ball of a nonunital star subalgebra of
`B(H)` is both ultraweakly and, by compatible convex-closure transfer, Mackey dense in the unit
ball of its WOT closure.
-/

@[expose] public section

open Set
open scoped InnerProductSpace Ultraweak

noncomputable section

namespace Ultraweak

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The ultraweak closure of the unit ball of a bounded-operator star subalgebra is the unit ball
of its Mathlib-WOT closure. -/
theorem ultraweak_closure_unitBall_eq_wotClosure_unitBall
    (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)) :
    closure (ofUltraweak ⁻¹'
        ((S : Set (H →L[ℂ] H)) ∩ Metric.closedBall 0 1) :
          Set σ(H →L[ℂ] H, ContinuousLinearMap.VectorFunctionalPredual ℂ H H)) =
      (ofUltraweak ⁻¹'
        ((S.wotClosure : Set (H →L[ℂ] H)) ∩ Metric.closedBall 0 1) :
          Set σ(H →L[ℂ] H, ContinuousLinearMap.VectorFunctionalPredual ℂ H H)) := by
  apply SakaiInvariantTestSpace.ultraweak_closure_subalgebra_unitBall_of_testWeakClosure_eq
    ContinuousLinearMap.vectorFunctionalPredualSpan_sakaiInvariant S S.wotClosure
  exact testWeakClosure_vectorFunctionalPredualSpan_eq_wotClosure S

/-- The unit ball of a bounded-operator star subalgebra is Mackey dense in the unit ball of its
Mathlib-WOT closure. -/
theorem kaplansky_density_wotClosure
    (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)) :
    closure (ofMackey ⁻¹'
        ((S : Set (H →L[ℂ] H)) ∩ Metric.closedBall 0 1) :
          Set (SakaiMackey (M := H →L[ℂ] H)
            (⊤ : Submodule ℂ
              (ContinuousLinearMap.VectorFunctionalPredual ℂ H H)))) =
      (ofMackey ⁻¹'
        ((S.wotClosure : Set (H →L[ℂ] H)) ∩ Metric.closedBall 0 1) :
          Set (SakaiMackey (M := H →L[ℂ] H)
            (⊤ : Submodule ℂ
              (ContinuousLinearMap.VectorFunctionalPredual ℂ H H)))) := by
  apply SakaiInvariantTestSpace.kaplansky_density_of_testWeakClosure_eq
    ContinuousLinearMap.vectorFunctionalPredualSpan_sakaiInvariant S S.wotClosure
  exact testWeakClosure_vectorFunctionalPredualSpan_eq_wotClosure S

end Ultraweak
