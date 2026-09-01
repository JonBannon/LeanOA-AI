import LeanOA.ComplexOrder
import LeanOA.Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Sakai 1.13 complete-additivity scratch test

This file is deliberately outside the production import graph.  It tests the arbitrary-index
scalar summation semantics in Sakai 1.13.4 and the easy implication from normality on projections
to complete additivity, while making no permanent API decision.
-/

open Filter Set
open scoped BigOperators ComplexOrder Topology

namespace SakaiCompleteAdditivityScratch

/-- For nonnegative complex terms, Mathlib's unconditional `HasSum` semantics is exactly the
least-upper-bound semantics of the net of all finite partial sums.

The order on `ℂ` is Sak-AI's `ComplexOrder`.  Nonnegative elements therefore have zero imaginary
part, and the existing supremum-convergence instance turns the order LUB into ordinary complex
convergence. -/
theorem hasSum_iff_isLUB_finsetSum_of_nonneg
    {ι : Type*} {f : ι → ℂ} (hf : ∀ i, 0 ≤ f i) {a : ℂ} :
    HasSum f a ↔ IsLUB (Set.range (fun s : Finset ι ↦ ∑ i ∈ s, f i)) a := by
  have hmono : Monotone (fun s : Finset ι ↦ ∑ i ∈ s, f i) :=
    Finset.sum_mono_set_of_nonneg hf
  constructor
  · intro h
    exact isLUB_of_tendsto_atTop hmono h
  · intro h
    exact tendsto_atTop_isLUB hmono h

section Forward

variable {M : Type*} [NonUnitalCStarAlgebra M] [PartialOrder M]

/-- Scratch form of normality implying complete additivity.

`P` is the finite-partial-sum projection supplied explicitly by the caller.  Thus this theorem
does not depend on the names or implementation choices of the parallel orthogonal-projection
workstream.  Its hypotheses are precisely the reusable interface that workstream must provide:
the underlying finite sum, monotonicity, and its projection-order least upper bound. -/
theorem normal_hasSum_of_partialSum_isLUB
    (φ : M →ₚ[ℂ] ℂ) (hφ : φ.IsNormalOnProjections)
    {ι : Type*} (p : ι → {p : M // IsStarProjection p})
    (P : Finset ι → {p : M // IsStarProjection p})
    (hP : ∀ s, (P s).1 = ∑ i ∈ s, (p i).1)
    (hPmono : Monotone P)
    (q : {p : M // IsStarProjection p})
    (hPq : IsLUB (Set.range P) q) :
    HasSum (fun i ↦ φ (p i).1) (φ q.1) := by
  have hscalar :
      IsLUB (Set.range (fun s : Finset ι ↦ φ (P s).1)) (φ q.1) := by
    have h := hφ (Set.range_nonempty P)
      (directedOn_range.mpr hPmono.directed_le) hPq
    change IsLUB
      (Set.range ((fun r : {p : M // IsStarProjection p} ↦ φ r.1) ∘ P)) (φ q.1)
    rw [Set.range_comp]
    exact h
  have hscalar_mono : Monotone (fun s : Finset ι ↦ φ (P s).1) :=
    hφ.monotone.comp hPmono
  have htendsto :
      Tendsto (fun s : Finset ι ↦ φ (P s).1) atTop (nhds (φ q.1)) :=
    tendsto_atTop_isLUB hscalar_mono hscalar
  change Tendsto (fun s : Finset ι ↦ ∑ i ∈ s, φ (p i).1) atTop (nhds (φ q.1))
  convert htendsto using 1
  funext s
  rw [hP]
  exact (map_sum φ.toLinearMap _ _).symm

end Forward

section ConverseBoundary

variable {M : Type*} [NonUnitalCStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

/-- Once an orthogonal decomposition of a projection LUB has finite partial sums dominated by the
original directed family, complete additivity supplies preservation of that LUB.

This lemma isolates the exact missing input in the converse.  For the source proof it is enough to
construct such a decomposition for a nonempty chain of projections; the existing cutoff/Zorn
argument can then be generalized from full Scott continuity to chain-LUB continuity. -/
theorem isLUB_apply_of_hasSum_of_finset_domination
    (φ : M →ₚ[ℂ] ℂ)
    {c : Set {p : M // IsStarProjection p}} {q : {p : M // IsStarProjection p}}
    (hcq : IsLUB c q)
    {ι : Type*} (e : ι → {p : M // IsStarProjection p})
    (E : Finset ι → {p : M // IsStarProjection p})
    (hE : ∀ s, (E s).1 = ∑ i ∈ s, (e i).1)
    (hsum : HasSum (fun i ↦ φ (e i).1) (φ q.1))
    (hdom : ∀ s, ∃ r ∈ c, E s ≤ r) :
    IsLUB ((fun r : {p : M // IsStarProjection p} ↦ φ r.1) '' c) (φ q.1) := by
  constructor
  · rintro _ ⟨r, hr, rfl⟩
    exact φ.monotone (hcq.1 hr)
  · intro b hb
    have hscalar :=
      (hasSum_iff_isLUB_finsetSum_of_nonneg
        (fun i ↦ φ.map_nonneg (e i).2.nonneg)).mp hsum
    apply hscalar.2
    rintro _ ⟨s, rfl⟩
    obtain ⟨r, hr, hEr⟩ := hdom s
    calc
      (∑ i ∈ s, φ (e i).1) = φ (E s).1 := by
        rw [hE]
        exact (map_sum φ.toLinearMap _ _).symm
      _ ≤ φ r.1 := φ.monotone hEr
      _ ≤ b := hb ⟨r, hr, rfl⟩

#print axioms hasSum_iff_isLUB_finsetSum_of_nonneg
#print axioms normal_hasSum_of_partialSum_isLUB
#print axioms isLUB_apply_of_hasSum_of_finset_domination

end ConverseBoundary

end SakaiCompleteAdditivityScratch
