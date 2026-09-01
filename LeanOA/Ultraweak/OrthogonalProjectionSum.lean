module

public import LeanOA.Ultraweak.StrongProjection

import LeanOA.Mathlib.Analysis.CStarAlgebra.Projection

@[expose] public section

/-!
# Finite partial sums of orthogonal projections

This file packages the finite-subset net associated to an arbitrary pairwise orthogonal family of
projections. Its least upper bound is the existing supremum in the projection lattice of a
$W^*$-algebra, and the existing projection convergence API supplies both ultraweak and intrinsic
strong convergence.
-/

open Filter Set
open scoped Topology Ultraweak

namespace IsStarProjection

section Algebra

variable {R I : Type*} [NonUnitalNonAssocSemiring R] [StarAddMonoid R]

private theorem mul_finsetSum_of_mem (p : I → R) (hp : ∀ i, IsStarProjection (p i))
    (horth : Pairwise fun i j ↦ p i * p j = 0) {i : I} {s : Finset I} (hi : i ∈ s) :
    p i * ∑ j ∈ s, p j = p i := by
  classical
  rw [Finset.mul_sum, Finset.sum_eq_single i]
  · exact (hp i).isIdempotentElem.eq
  · intro j _ hji
    exact horth hji.symm
  · exact fun hnot ↦ (hnot hi).elim

omit [StarAddMonoid R] in
private theorem mul_finsetSum_of_notMem (p : I → R)
    (horth : Pairwise fun i j ↦ p i * p j = 0) {i : I} {s : Finset I} (hi : i ∉ s) :
    p i * ∑ j ∈ s, p j = 0 := by
  rw [Finset.mul_sum]
  exact Finset.sum_eq_zero fun j hj ↦ horth fun hij ↦ hi (hij ▸ hj)

/-- A finite sum from a pairwise orthogonal family of star projections is a star projection. -/
theorem finset_sum (p : I → R) (hp : ∀ i, IsStarProjection (p i))
    (horth : Pairwise fun i j ↦ p i * p j = 0) (s : Finset I) :
    IsStarProjection (∑ i ∈ s, p i) := by
  classical
  refine ⟨?_, isSelfAdjoint_sum s fun i _ ↦ (hp i).isSelfAdjoint⟩
  change (∑ i ∈ s, p i) * (∑ i ∈ s, p i) = ∑ i ∈ s, p i
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun i hi ↦ mul_finsetSum_of_mem p hp horth hi

/-- The finite partial sum of a pairwise orthogonal projection family, bundled as a projection. -/
def orthogonalFinsetSum
    (p : I → {q : R // IsStarProjection q})
    (horth : Pairwise fun i j ↦ (p i).1 * (p j).1 = 0)
    (s : Finset I) : {q : R // IsStarProjection q} :=
  ⟨∑ i ∈ s, (p i).1,
    finset_sum (fun i ↦ (p i).1) (fun i ↦ (p i).2) horth s⟩

@[simp]
theorem coe_orthogonalFinsetSum
    (p : I → {q : R // IsStarProjection q})
    (horth : Pairwise fun i j ↦ (p i).1 * (p j).1 = 0)
    (s : Finset I) :
    (orthogonalFinsetSum p horth s).1 = ∑ i ∈ s, (p i).1 := rfl

/-- Partial sums over disjoint finite index sets are orthogonal. -/
theorem orthogonalFinsetSum_mul_eq_zero_of_disjoint
    (p : I → {q : R // IsStarProjection q})
    (horth : Pairwise fun i j ↦ (p i).1 * (p j).1 = 0)
    {s t : Finset I} (hst : Disjoint s t) :
    (orthogonalFinsetSum p horth s).1 * (orthogonalFinsetSum p horth t).1 = 0 := by
  classical
  change (∑ i ∈ s, (p i).1) * (∑ j ∈ t, (p j).1) = 0
  rw [Finset.sum_mul]
  exact Finset.sum_eq_zero fun i hi ↦
    mul_finsetSum_of_notMem (fun i ↦ (p i).1) horth fun hit ↦
      Finset.disjoint_left.mp hst hi hit

/-- A disjoint union gives the sum of the corresponding finite partial sums. -/
theorem coe_orthogonalFinsetSum_union_of_disjoint
    (p : I → {q : R // IsStarProjection q})
    (horth : Pairwise fun i j ↦ (p i).1 * (p j).1 = 0)
    [DecidableEq I] {s t : Finset I} (hst : Disjoint s t) :
    (orthogonalFinsetSum p horth (s ∪ t)).1 =
      (orthogonalFinsetSum p horth s).1 + (orthogonalFinsetSum p horth t).1 := by
  exact Finset.sum_union hst

end Algebra

section Order

variable {M I : Type*} [NonUnitalCStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

/-- Finite partial sums of a pairwise orthogonal projection family increase under inclusion. -/
theorem orthogonalFinsetSum_mono
    (p : I → {q : M // IsStarProjection q})
    (horth : Pairwise fun i j ↦ (p i).1 * (p j).1 = 0) :
    Monotone (orthogonalFinsetSum p horth) := by
  classical
  intro s t hst
  apply (orthogonalFinsetSum p horth s).2.le_of_mul_eq_left
    (orthogonalFinsetSum p horth t).2
  change (∑ i ∈ s, (p i).1) * (∑ j ∈ t, (p j).1) = ∑ i ∈ s, (p i).1
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun i hi ↦
    mul_finsetSum_of_mem (fun i ↦ (p i).1) (fun i ↦ (p i).2) horth (hst hi)

/-- A member of a finite orthogonal projection family lies below its partial sum. -/
theorem le_orthogonalFinsetSum_of_mem
    (p : I → {q : M // IsStarProjection q})
    (horth : Pairwise fun i j ↦ (p i).1 * (p j).1 = 0)
    {i : I} {s : Finset I} (hi : i ∈ s) :
    p i ≤ orthogonalFinsetSum p horth s := by
  classical
  apply (p i).2.le_of_mul_eq_left (orthogonalFinsetSum p horth s).2
  exact mul_finsetSum_of_mem (fun i ↦ (p i).1) (fun i ↦ (p i).2) horth hi

/-- A finite orthogonal sum lies below any projection which dominates every summand. -/
theorem orthogonalFinsetSum_le_of_forall_le
    (p : I → {q : M // IsStarProjection q})
    (horth : Pairwise fun i j ↦ (p i).1 * (p j).1 = 0)
    {s : Finset I} {r : {q : M // IsStarProjection q}}
    (h : ∀ i ∈ s, p i ≤ r) :
    orthogonalFinsetSum p horth s ≤ r := by
  classical
  apply (orthogonalFinsetSum p horth s).2.le_of_mul_eq_left r.2
  change (∑ i ∈ s, (p i).1) * r.1 = ∑ i ∈ s, (p i).1
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun i hi ↦
    ((p i).2.le_iff_mul_eq_left r.2).mp (h i hi)

private theorem tendsto_range_orthogonalFinsetSum
    (p : I → {q : M // IsStarProjection q})
    (horth : Pairwise fun i j ↦ (p i).1 * (p j).1 = 0) :
    Tendsto
      (fun s : Finset I ↦
        (⟨orthogonalFinsetSum p horth s, Set.mem_range_self s⟩ :
          {q // q ∈ Set.range (orthogonalFinsetSum p horth)}))
      atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro q
  obtain ⟨_, s, rfl⟩ := q
  exact ⟨s, fun t hst ↦ orthogonalFinsetSum_mono p horth hst⟩

end Order

section WStar

variable {M P I : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [WStarAlgebra M]

/-- Every finite partial sum lies below the projection supremum of the family. -/
theorem orthogonalFinsetSum_le_iSup
    (p : I → {q : M // IsStarProjection q})
    (horth : Pairwise fun i j ↦ (p i).1 * (p j).1 = 0)
    (s : Finset I) :
    orthogonalFinsetSum p horth s ≤ ⨆ i, p i := by
  classical
  apply (orthogonalFinsetSum p horth s).2.le_of_mul_eq_left (⨆ i, p i).2
  change (∑ i ∈ s, (p i).1) * (⨆ i, p i).1 = ∑ i ∈ s, (p i).1
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ ↦
    ((p i).2.le_iff_mul_eq_left (⨆ i, p i).2).mp (le_iSup p i)

/-- The projection supremum of a pairwise orthogonal family is the least upper bound of its finite
partial sums. -/
theorem isLUB_range_orthogonalFinsetSum
    (p : I → {q : M // IsStarProjection q})
    (horth : Pairwise fun i j ↦ (p i).1 * (p j).1 = 0) :
    IsLUB (Set.range (orthogonalFinsetSum p horth)) (⨆ i, p i) := by
  constructor
  · rintro q ⟨s, rfl⟩
    exact orthogonalFinsetSum_le_iSup p horth s
  · intro q hq
    exact iSup_le fun i ↦ hq ⟨{i}, by
      ext
      simp [orthogonalFinsetSum]
    ⟩

/-- The projection supremum is also the ambient least upper bound of the underlying partial sums. -/
theorem isLUB_range_coe_orthogonalFinsetSum
    (p : I → {q : M // IsStarProjection q})
    (horth : Pairwise fun i j ↦ (p i).1 * (p j).1 = 0) :
    IsLUB
      (Set.range fun s : Finset I ↦ (orthogonalFinsetSum p horth s).1)
      (⨆ i, p i).1 := by
  let q := orthogonalFinsetSum p horth
  have hmono : Monotone q := orthogonalFinsetSum_mono p horth
  have hLUB := IsStarProjection.isLUB_coe_of_isLUB
    (WStarAlgebra.predual M) (Set.range q)
    hmono.directed_le.directedOn_range (Set.range_nonempty q)
    (isLUB_range_orthogonalFinsetSum p horth)
  simpa only [← Set.range_comp, Function.comp_def, q] using hLUB

variable [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]

/-- Finite partial sums of a pairwise orthogonal projection family converge ultraweakly to its
projection supremum. -/
theorem tendsto_toUltraweak_orthogonalFinsetSum
    (p : I → {q : M // IsStarProjection q})
    (horth : Pairwise fun i j ↦ (p i).1 * (p j).1 = 0) :
    Tendsto
      (fun s : Finset I ↦ toUltraweak ℂ P (orthogonalFinsetSum p horth s).1)
      atTop (nhds (toUltraweak ℂ P (⨆ i, p i).1)) := by
  let q := orthogonalFinsetSum p horth
  have hmono : Monotone q := orthogonalFinsetSum_mono p horth
  have hcanonical := IsStarProjection.tendsto_toUltraweak_of_isLUB
    (P := P) (Set.range q) hmono.directed_le.directedOn_range
    (Set.range_nonempty q) (isLUB_range_orthogonalFinsetSum p horth)
  exact hcanonical.comp (tendsto_range_orthogonalFinsetSum p horth)

/-- Finite partial sums of a pairwise orthogonal projection family converge in the intrinsic
strong topology to its projection supremum. -/
theorem tendsto_toStrong_orthogonalFinsetSum
    (p : I → {q : M // IsStarProjection q})
    (horth : Pairwise fun i j ↦ (p i).1 * (p j).1 = 0) :
    Tendsto
      (fun s : Finset I ↦ Ultraweak.toStrong P (orthogonalFinsetSum p horth s).1)
      atTop (nhds (Ultraweak.toStrong P (⨆ i, p i).1)) := by
  let q := orthogonalFinsetSum p horth
  have hmono : Monotone q := orthogonalFinsetSum_mono p horth
  have hcanonical := Ultraweak.Strong.tendsto_toStrong_of_isLUB
    (P := P) (Set.range q) hmono.directed_le.directedOn_range
    (Set.range_nonempty q) (isLUB_range_orthogonalFinsetSum p horth)
  exact hcanonical.comp (tendsto_range_orthogonalFinsetSum p horth)

end WStar

end IsStarProjection
