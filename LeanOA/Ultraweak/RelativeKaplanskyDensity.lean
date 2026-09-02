module

public import LeanOA.Ultraweak.TestWeak

/-!
# Ambient-relative Kaplansky density

This file proves Kaplansky unit-ball density inside an explicitly supplied test-weak closure.
Both source and target remain nonunital star subalgebras of the same ambient dual C-star algebra;
no second predual or competing topology-bearing carrier is introduced.
-/

@[expose] public section

open Set
open scoped Ultraweak

noncomputable section

namespace Ultraweak.SakaiInvariantTestSpace

variable {M P : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]

/-- Closed-source relative Krein--Milman step for Kaplansky density. -/
theorem ultraweak_closure_closed_subalgebra_unitBall_of_testWeakClosure_eq
    {V : Submodule ℂ P}
    (hV : SakaiInvariantTestSpace (M := M) V)
    (S T : NonUnitalStarSubalgebra ℂ M) [IsClosed (S : Set M)]
    (hST : testWeakClosure (M := M) V (S : Set M) = (T : Set M)) :
    closure (ofUltraweak ⁻¹'
        ((S : Set M) ∩ Metric.closedBall (0 : M) 1) : Set σ(M, P)) =
      (ofUltraweak ⁻¹'
        ((T : Set M) ∩ Metric.closedBall (0 : M) 1) : Set σ(M, P)) := by
  let C : Set σ(M, P) :=
    ofUltraweak ⁻¹' ((S : Set M) ∩ Metric.closedBall (0 : M) 1)
  let B : Set σ(M, P) :=
    ofUltraweak ⁻¹' ((T : Set M) ∩ Metric.closedBall (0 : M) 1)
  letI : Module ℝ M := RestrictScalars.module ℝ ℂ M
  letI : IsScalarTower ℝ ℂ M := RestrictScalars.isScalarTower ℝ ℂ M
  letI : Module ℝ σ(M, P) := RestrictScalars.module ℝ ℂ σ(M, P)
  letI : IsScalarTower ℝ ℂ σ(M, P) := RestrictScalars.isScalarTower ℝ ℂ σ(M, P)
  letI : LocallyConvexSpace ℝ σ(M, P) := WeakBilin.locallyConvexSpace
  have hTuw : IsClosed (ofUltraweak ⁻¹' (T : Set M) : Set σ(M, P)) := by
    rw [← hST]
    exact isClosed_ultraweak_testWeakClosure V (S : Set M)
  have hTnorm : IsClosed (T : Set M) := by
    rw [← hST]
    exact isClosed_testWeakClosure V (S : Set M)
  letI : IsClosed (T : Set M) := hTnorm
  letI : NonUnitalCStarAlgebra T :=
    NonUnitalStarSubalgebra.nonUnitalCStarAlgebra T
  have hSTle : S ≤ T := by
    intro y hy
    change y ∈ (T : Set M)
    rw [← hST]
    exact subset_testWeakClosure V (S : Set M) hy
  have hBcompact : IsCompact B := by
    change IsCompact
      ((ofUltraweak ⁻¹' (T : Set M) : Set σ(M, P)) ∩
        (ofUltraweak ⁻¹' Metric.closedBall (0 : M) 1 : Set σ(M, P)))
    exact (Ultraweak.isCompact_closedBall ℂ P (0 : M) 1).inter_left hTuw
  have hBconv : Convex ℝ B := by
    let TR := T.toNonUnitalSubalgebra.toSubmodule.restrictScalars ℝ
    have hTint : Convex ℝ ((T : Set M) ∩ Metric.closedBall (0 : M) 1) :=
      TR.convex.inter (convex_closedBall (0 : M) 1)
    exact hTint.linear_preimage
      ((Ultraweak.linearEquiv ℂ M P).restrictScalars ℝ).toLinearMap
  have hCconv : Convex ℝ C := by
    let SR := S.toNonUnitalSubalgebra.toSubmodule.restrictScalars ℝ
    have hSint : Convex ℝ ((S : Set M) ∩ Metric.closedBall (0 : M) 1) :=
      SR.convex.inter (convex_closedBall (0 : M) 1)
    exact hSint.linear_preimage
      ((Ultraweak.linearEquiv ℂ M P).restrictScalars ℝ).toLinearMap
  have hExtreme : B.extremePoints ℝ ⊆ closure C := by
    intro x hx
    let e : σ(M, P) ≃ₗ[ℝ] M := (Ultraweak.linearEquiv ℂ M P).restrictScalars ℝ
    have heB : e '' B = (T : Set M) ∩ Metric.closedBall (0 : M) 1 := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · intro hy
        exact ⟨e.symm y, hy, e.apply_symm_apply y⟩
    have hex : ofUltraweak x ∈
        ((T : Set M) ∩ Metric.closedBall (0 : M) 1).extremePoints ℝ := by
      have hx' : e x ∈ e '' B.extremePoints ℝ := ⟨x, hx, rfl⟩
      rw [image_extremePoints, heB] at hx'
      exact hx'
    let xt : T := ⟨ofUltraweak x, hex.1.1⟩
    have hxt : xt ∈ extremePoints ℝ (Metric.closedBall (0 : T) 1) := by
      apply (NonUnitalStarSubalgebra.coe_mem_extremePoints_unitClosedBall_iff T xt).mp
      simpa only [xt] using hex
    have hcubicT := star_self_conjugate_eq_self_of_mem_extremePoints_unitClosedBall hxt
    have hcubic : ofUltraweak x * star (ofUltraweak x) * ofUltraweak x = ofUltraweak x := by
      have hcubic' := congrArg (fun y : T ↦ (y : M)) hcubicT
      change ofUltraweak x * star (ofUltraweak x) * ofUltraweak x = ofUltraweak x at hcubic'
      exact hcubic'
    have hmem := kaplanskyTransform_mem_ultraweak_closure_of_mem_testWeakClosure
      hV S (a := ofUltraweak x) (by rw [hST]; exact hex.1.1)
    rw [CStarAlgebra.kaplanskyTransform_eq_self_of_star_self_conjugate_eq_self hcubic] at hmem
    exact hmem
  apply Set.Subset.antisymm
  · exact closure_minimal (fun _ hx ↦ ⟨hSTle hx.1, hx.2⟩) hBcompact.isClosed
  · change B ⊆ closure C
    rw [← closure_convexHull_extremePoints hBcompact hBconv]
    have hclosureConv : Convex ℝ (closure C) := hCconv.closure
    have hhull : convexHull ℝ (B.extremePoints ℝ) ⊆ closure C :=
      convexHull_min hExtreme hclosureConv
    simpa only [closure_closure] using closure_mono hhull

/-- Relative ultraweak unit-ball density for an arbitrary source star subalgebra. -/
theorem ultraweak_closure_subalgebra_unitBall_of_testWeakClosure_eq
    {V : Submodule ℂ P}
    (hV : SakaiInvariantTestSpace (M := M) V)
    (S T : NonUnitalStarSubalgebra ℂ M)
    (hST : testWeakClosure (M := M) V (S : Set M) = (T : Set M)) :
    closure (ofUltraweak ⁻¹'
        ((S : Set M) ∩ Metric.closedBall (0 : M) 1) : Set σ(M, P)) =
      (ofUltraweak ⁻¹'
        ((T : Set M) ∩ Metric.closedBall (0 : M) 1) : Set σ(M, P)) := by
  let U := S.topologicalClosure
  letI : IsClosed (U : Set M) := S.isClosed_topologicalClosure
  have hTtest : IsClosed
      ((WeakBilin.linearEquiv ℂ (testPairing (M := M) V)) ⁻¹' (T : Set M)) := by
    rw [← hST, preimage_testWeakClosure]
    exact isClosed_closure
  have hTnorm : IsClosed (T : Set M) := by
    rw [← hST]
    exact isClosed_testWeakClosure V (S : Set M)
  have hSTle : (S : Set M) ⊆ (T : Set M) := by
    rw [← hST]
    exact subset_testWeakClosure V (S : Set M)
  have hUTle : (U : Set M) ⊆ (T : Set M) :=
    closure_minimal hSTle hTnorm
  have hUT : testWeakClosure (M := M) V (U : Set M) = (T : Set M) := by
    apply Set.Subset.antisymm
    · exact testWeakClosure_minimal V hUTle hTtest
    · rw [← hST]
      exact testWeakClosure_mono V S.le_topologicalClosure
  have hrealconv : Convex ℝ (S : Set M) :=
    (S.toNonUnitalSubalgebra.toSubmodule.restrictScalars ℝ).convex
  have hnormClosure :
      closure ((S : Set M) ∩ Metric.closedBall (0 : M) 1) =
        (U : Set M) ∩ Metric.closedBall (0 : M) 1 := by
    change closure ((S : Set M) ∩ Metric.closedBall (0 : M) 1) =
      closure (S : Set M) ∩ Metric.closedBall (0 : M) 1
    exact hrealconv.closure_inter_unitClosedBall S.zero_mem
  have hUU :
      (ofUltraweak ⁻¹' ((U : Set M) ∩ Metric.closedBall (0 : M) 1) : Set σ(M, P)) ⊆
        closure (ofUltraweak ⁻¹'
          ((S : Set M) ∩ Metric.closedBall (0 : M) 1) : Set σ(M, P)) := by
    intro x hx
    have hxnorm : ofUltraweak x ∈
        closure ((S : Set M) ∩ Metric.closedBall (0 : M) 1) := by
      rw [hnormClosure]
      exact hx
    have hmap := map_mem_closure
      (continuous_toUltraweak (𝕜 := ℂ) (M := M) (P := P)) hxnorm
      (t := ofUltraweak ⁻¹'
        ((S : Set M) ∩ Metric.closedBall (0 : M) 1)) (by
          intro y hy
          simpa using hy)
    simpa using hmap
  have hUW_U :=
    ultraweak_closure_closed_subalgebra_unitBall_of_testWeakClosure_eq hV U T hUT
  have hTuw : IsClosed (ofUltraweak ⁻¹' (T : Set M) : Set σ(M, P)) := by
    rw [← hST]
    exact isClosed_ultraweak_testWeakClosure V (S : Set M)
  have hBclosed : IsClosed
      (ofUltraweak ⁻¹'
        ((T : Set M) ∩ Metric.closedBall (0 : M) 1) : Set σ(M, P)) :=
    hTuw.inter (Ultraweak.isClosed_closedBall ℂ P 0 1)
  apply Set.Subset.antisymm
  · exact closure_minimal (fun _ hx ↦ ⟨hSTle hx.1, hx.2⟩) hBclosed
  · calc
      (ofUltraweak ⁻¹'
          ((T : Set M) ∩ Metric.closedBall (0 : M) 1) : Set σ(M, P)) =
          closure (ofUltraweak ⁻¹'
            ((U : Set M) ∩ Metric.closedBall (0 : M) 1) : Set σ(M, P)) := hUW_U.symm
      _ ⊆ closure (closure (ofUltraweak ⁻¹'
          ((S : Set M) ∩ Metric.closedBall (0 : M) 1) : Set σ(M, P))) :=
        closure_mono hUU
      _ = closure (ofUltraweak ⁻¹'
          ((S : Set M) ∩ Metric.closedBall (0 : M) 1) : Set σ(M, P)) := closure_closure

/-- Kaplansky unit-ball density inside an explicitly identified test-weak closure. -/
theorem kaplansky_density_of_testWeakClosure_eq
    {V : Submodule ℂ P}
    (hV : SakaiInvariantTestSpace (M := M) V)
    (S T : NonUnitalStarSubalgebra ℂ M)
    (hST : testWeakClosure (M := M) V (S : Set M) = (T : Set M)) :
    closure (ofMackey ⁻¹'
        ((S : Set M) ∩ Metric.closedBall (0 : M) 1) :
          Set (SakaiMackey (M := M) (⊤ : Submodule ℂ P))) =
      (ofMackey ⁻¹'
        ((T : Set M) ∩ Metric.closedBall (0 : M) 1) :
          Set (SakaiMackey (M := M) (⊤ : Submodule ℂ P))) := by
  apply mackey_closure_of_ultraweak_closure
  · exact (S.toNonUnitalSubalgebra.toSubmodule.restrictScalars ℝ).convex.inter
      (convex_closedBall (0 : M) 1)
  · exact ultraweak_closure_subalgebra_unitBall_of_testWeakClosure_eq hV S T hST

end Ultraweak.SakaiInvariantTestSpace
