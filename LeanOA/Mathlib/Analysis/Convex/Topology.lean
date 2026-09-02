module

public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.Normed.Module.RCLike.Real

@[expose] public section

open Set

/-- If two convex sets meet in the interior of the second set, then closure commutes with their
intersection.  The result is asymmetric only in its hypothesis: it is enough to have an interior
point of the second set which belongs to the first.

This is the topological-vector-space result behind the familiar fact that intersecting a dense
linear subspace with a closed ball leaves it dense in that ball. -/
theorem Convex.closure_inter_of_inter_interior_nonempty
    {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [TopologicalSpace 𝕜] [OrderTopology 𝕜]
    [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [Module 𝕜 E] [ContinuousSMul 𝕜 E] {C D : Set E}
    (hC : Convex 𝕜 C) (hD : Convex 𝕜 D) (hCD : (C ∩ interior D).Nonempty) :
    closure (C ∩ D) = closure C ∩ closure D := by
  apply Set.Subset.antisymm
  · exact closure_inter_subset_inter_closure _ _
  · rintro x ⟨hxC, hxD⟩
    obtain ⟨z, hzC, hzD⟩ := hCD
    have hopen : openSegment 𝕜 z x ⊆ closure C ∩ interior D := by
      intro y hy
      exact ⟨hC.closure.openSegment_subset (subset_closure hzC) hxC hy,
        hD.openSegment_interior_closure_subset_interior hzD hxD hy⟩
    have hinter : closure C ∩ interior D ⊆ closure (C ∩ D) := by
      refine (isOpen_interior.closure_inter).trans (closure_mono ?_)
      exact inter_subset_inter_right C interior_subset
    exact closure_minimal (hopen.trans hinter) isClosed_closure
      (segment_subset_closure_openSegment (right_mem_segment (𝕜 := 𝕜) z x))

/-- Intersecting a convex set with a positive-radius closed ball centered at one of its points
commutes with closure. -/
theorem Convex.closure_inter_closedBall {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] {C : Set E}
    (hC : Convex ℝ C) {c : E} (hc : c ∈ C) {r : ℝ} (hr : 0 < r) :
    closure (C ∩ Metric.closedBall c r) = closure C ∩ Metric.closedBall c r := by
  rw [hC.closure_inter_of_inter_interior_nonempty (convex_closedBall c r) ⟨c, hc, by
    apply interior_mono Metric.ball_subset_closedBall
    rw [Metric.isOpen_ball.interior_eq]
    exact Metric.mem_ball_self hr⟩, Metric.isClosed_closedBall.closure_eq]

/-- Intersecting a convex set containing zero with the closed unit ball commutes with closure. -/
theorem Convex.closure_inter_unitClosedBall {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] {C : Set E}
    (hC : Convex ℝ C) (h0 : (0 : E) ∈ C) :
    closure (C ∩ Metric.closedBall (0 : E) 1) =
      closure C ∩ Metric.closedBall (0 : E) 1 :=
  hC.closure_inter_closedBall h0 zero_lt_one

namespace Submodule

/-- Extreme points of the unit ball of a real subspace are exactly the extreme points of its
ambient unit-ball carrier. -/
theorem coe_mem_extremePoints_unitClosedBall_iff
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (T : Submodule ℝ E) (x : T) :
    (x : E) ∈ extremePoints ℝ ((T : Set E) ∩ Metric.closedBall 0 1) ↔
      x ∈ extremePoints ℝ (Metric.closedBall 0 1) := by
  let e : T →ₗ[ℝ] E := T.subtype
  simp only [mem_extremePoints_iff_left, mem_inter_iff, mem_closedBall_zero_iff]
  constructor
  · rintro ⟨⟨_, hxnorm⟩, hx⟩
    refine ⟨hxnorm, ?_⟩
    intro y hy z hz hxyz
    apply Subtype.ext
    apply hx (y : E) ⟨y.property, hy⟩ (z : E) ⟨z.property, hz⟩
    have himage := image_openSegment ℝ e.toAffineMap y z
    have hximage : e.toAffineMap x ∈ e.toAffineMap '' openSegment ℝ y z :=
      ⟨x, hxyz, rfl⟩
    rw [himage] at hximage
    simpa [e] using hximage
  · rintro ⟨hxnorm, hx⟩
    refine ⟨⟨x.property, hxnorm⟩, ?_⟩
    intro y ⟨hyT, hynorm⟩ z ⟨hzT, hznorm⟩ hxyz
    let yT : T := ⟨y, hyT⟩
    let zT : T := ⟨z, hzT⟩
    have hxyz' : x ∈ openSegment ℝ yT zT := by
      have himage := image_openSegment ℝ e.toAffineMap yT zT
      have hxyzE : e.toAffineMap x ∈
          openSegment ℝ (e.toAffineMap yT) (e.toAffineMap zT) := by
        simpa [e, yT, zT] using hxyz
      rw [← himage] at hxyzE
      obtain ⟨w, hw, hweq⟩ := hxyzE
      have hwx : w = x := Subtype.ext (by simpa [e] using hweq)
      rwa [← hwx]
    exact congrArg Subtype.val (hx yT hynorm zT hznorm hxyz')

end Submodule
