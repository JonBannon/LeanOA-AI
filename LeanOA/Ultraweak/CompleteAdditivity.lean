module

public import LeanOA.Ultraweak.NormalOrder
public import LeanOA.Ultraweak.ProjectionChain
public import Mathlib.Topology.Algebra.InfiniteSum.Order

@[expose] public section

/-!
# Complete additivity of positive functionals

This file characterizes the canonical projection-normality predicate by complete additivity on
arbitrary mutually orthogonal projection families.  The scalar sum is Mathlib's `HasSum`, hence
the limit of the net of all finite subsums; no countability hypothesis or `tsum` default value is
involved.

The API remains theorem-only.  In particular, it introduces no competing normality notion and no
bundled complete-additivity predicate.
-/

open Filter Set
open scoped BigOperators ComplexOrder Topology

namespace Complex

/-- For a nonnegative complex family, `HasSum` is equivalent to saying that its finite subsums
have the asserted least upper bound.  This is the scalar order semantics used by complete
additivity for positive functionals.

Mathlib's `isLUB_hasSum` supplies the forward implication.  The converse uses the supremum-
convergence instance of Sak-AI's order on `ℂ`. -/
theorem hasSum_iff_isLUB_finsetSum_of_nonneg
    {ι : Type*} {f : ι → ℂ} (hf : ∀ i, 0 ≤ f i) {a : ℂ} :
    HasSum f a ↔ IsLUB (Set.range (fun s : Finset ι ↦ ∑ i ∈ s, f i)) a := by
  constructor
  · exact isLUB_hasSum hf
  · exact tendsto_atTop_isLUB (Finset.sum_mono_set_of_nonneg hf)

end Complex

namespace PositiveLinearMap

universe u v

variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [WStarAlgebra M]

/-- A positive functional normal on projections is completely additive on every arbitrary
pairwise orthogonal projection family.

The index universe `v` is independent of the algebra universe `u`.  Thus the theorem retains
Sakai's arbitrary-cardinality quantifier: it assumes neither countability nor an enumeration of
the family. -/
theorem IsNormalOnProjections.hasSum_orthogonal
    {φ : M →ₚ[ℂ] ℂ} (hφ : φ.IsNormalOnProjections)
    {ι : Type v} (e : ι → {p : M // IsStarProjection p})
    (horth : Pairwise fun i j ↦ (e i).1 * (e j).1 = 0) :
    HasSum (fun i ↦ φ (e i).1) (φ (⨆ i, e i).1) := by
  apply (Complex.hasSum_iff_isLUB_finsetSum_of_nonneg
    (fun i ↦ φ.map_nonneg (e i).2.nonneg)).2
  let E := IsStarProjection.orthogonalFinsetSum e horth
  have hnormal := hφ (Set.range_nonempty E)
    (directedOn_range.mpr
      (IsStarProjection.orthogonalFinsetSum_mono e horth).directed_le)
    (IsStarProjection.isLUB_range_orthogonalFinsetSum e horth)
  have hscalar :
      IsLUB (Set.range (fun s : Finset ι ↦ φ (E s).1)) (φ (⨆ i, e i).1) := by
    change IsLUB
      (Set.range ((fun r : {p : M // IsStarProjection p} ↦ φ r.1) ∘ E))
      (φ (⨆ i, e i).1)
    rw [Set.range_comp]
    exact hnormal
  simpa only [E, IsStarProjection.coe_orthogonalFinsetSum, map_sum] using hscalar

/-- If a positive functional is completely additive on all pairwise orthogonal projection
families indexed in the algebra's universe, then it is normal on projections.

The same-universe quantifier is sufficient because the maximal orthogonal decomposition of a
projection chain is indexed by a subtype of the projection type.  After normality is recovered,
`IsNormalOnProjections.hasSum_orthogonal` gives complete additivity for index types in every
universe. -/
theorem isNormalOnProjections_of_hasSum_orthogonal
    (φ : M →ₚ[ℂ] ℂ)
    (hadd : ∀ {ι : Type u} (e : ι → {p : M // IsStarProjection p})
      (_horth : Pairwise fun i j ↦ (e i).1 * (e j).1 = 0),
      HasSum (fun i ↦ φ (e i).1) (φ (⨆ i, e i).1)) :
    φ.IsNormalOnProjections := by
  apply (isNormalOnProjections_iff_scottContinuousOn_chains φ).2
  intro c hc hnon _ q hcq
  obtain ⟨s, horth, hdom, hsup⟩ :=
    hc.exists_orthogonal_projection_family hnon hcq
  have hsum : HasSum (fun p : s ↦ φ p.1.1) (φ q.1) := by
    simpa only [hsup] using hadd (fun p : s ↦ p.1) horth
  have hscalar :
      IsLUB (Set.range (fun t : Finset s ↦ ∑ p ∈ t, φ p.1.1)) (φ q.1) :=
    (Complex.hasSum_iff_isLUB_finsetSum_of_nonneg
      (fun p : s ↦ φ.map_nonneg p.1.2.nonneg)).1 hsum
  constructor
  · rintro _ ⟨r, hr, rfl⟩
    exact φ.monotone (hcq.1 hr)
  · intro b hb
    apply hscalar.2
    rintro _ ⟨t, rfl⟩
    obtain ⟨r, hr, htr⟩ := hdom t
    calc
      (∑ p ∈ t, φ p.1.1) =
          φ (IsStarProjection.orthogonalFinsetSum (fun p : s ↦ p.1) horth t).1 := by
        rw [IsStarProjection.coe_orthogonalFinsetSum]
        exact (map_sum φ.toLinearMap _ _).symm
      _ ≤ φ r.1 := φ.monotone htr
      _ ≤ b := hb ⟨r, hr, rfl⟩

/-- A positive functional on a $W^*$-algebra is normal on projections exactly when it is
completely additive on all pairwise orthogonal projection families indexed in the algebra's
universe.

The reverse implication only needs this same-universe family class; the forward theorem above is
separately polymorphic in an arbitrary index universe. -/
theorem isNormalOnProjections_iff_hasSum_orthogonal (φ : M →ₚ[ℂ] ℂ) :
    φ.IsNormalOnProjections ↔
      ∀ {ι : Type u} (e : ι → {p : M // IsStarProjection p})
        (_horth : Pairwise fun i j ↦ (e i).1 * (e j).1 = 0),
        HasSum (fun i ↦ φ (e i).1) (φ (⨆ i, e i).1) := by
  constructor
  · exact fun hφ _ e horth ↦ hφ.hasSum_orthogonal e horth
  · exact isNormalOnProjections_of_hasSum_orthogonal φ

end PositiveLinearMap
