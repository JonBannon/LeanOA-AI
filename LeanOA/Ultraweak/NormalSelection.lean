module

public import LeanOA.Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
public import LeanOA.Ultraweak.ProjectionLattice
public import Mathlib.Order.Zorn

@[expose] public section

/-!
# A projection-selection lemma for normal positive functionals

Given two positive functionals which preserve least upper bounds of projection chains, a strict
inequality on a projection persists uniformly on all nonzero subprojections of some nonzero
subprojection. The main result is algebraic once nonempty chains of projections have suprema.
Separate normality wrappers accept directed completeness or use an explicit Banach predual to
supply full completeness.
-/

open Set
open scoped ComplexOrder

namespace PositiveLinearMap

section ChainCompleteProjectionOrder

variable {M : Type*} [NonUnitalCStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

omit [StarOrderedRing M] in
private lemma le_of_not_lt_apply (f g : M →ₚ[ℂ] ℂ) {q : M} (hq : 0 ≤ q)
    (h : ¬ f q < g q) : g q ≤ f q := by
  rw [Complex.le_def]
  have hf := Complex.nonneg_iff.mp (f.map_nonneg hq)
  have hg := Complex.nonneg_iff.mp (g.map_nonneg hq)
  exact ⟨le_of_not_gt fun hgf ↦ h ⟨hgf, hf.2.symm.trans hg.2⟩, hg.2.symm.trans hf.2⟩

/-- If two positive functionals preserve projection LUBs on chains and satisfy a strict inequality
on a projection, then the same strict inequality holds on every nonzero subprojection of some
nonzero subprojection, provided every nonempty chain of projections has a least upper bound.

The hypothesis itself forces the original projection to be nonzero. Both normality assumptions are
replaced by the weaker chain-Scott hypotheses actually consumed by the proof. The final hypothesis
is exactly the chain completeness used by Zorn's lemma, stated in the inherited projection order.
This avoids installing a second, potentially incoherent order through a bundled lattice
instance. -/
theorem exists_nonzero_subprojection_lt_of_scottContinuousOn_chains
    {f g : M →ₚ[ℂ] ℂ}
    (hf : ScottContinuousOn
      {s : Set {q : M // IsStarProjection q} | IsChain (· ≤ ·) s}
      (fun q ↦ f q.1))
    (hg : ScottContinuousOn
      {s : Set {q : M // IsStarProjection q} | IsChain (· ≤ ·) s}
      (fun q ↦ g q.1))
    (hcomplete : ∀ s : Set {q : M // IsStarProjection q}, s.Nonempty →
      IsChain (· ≤ ·) s → ∃ p, IsLUB s p) {p : M}
    (hp : IsStarProjection p) (hfg : f p < g p) :
    ∃ p₁ : M, IsStarProjection p₁ ∧ p₁ ≠ 0 ∧ p₁ ≤ p ∧
      ∀ {q : M}, IsStarProjection q → q ≠ 0 → q ≤ p₁ → f q < g q := by
  let p' : {q : M // IsStarProjection q} := ⟨p, hp⟩
  let S : Set {q : M // IsStarProjection q} := {q | q ≤ p' ∧ g q.1 ≤ f q.1}
  let z : {q : M // IsStarProjection q} := ⟨0, IsStarProjection.zero M⟩
  have hz : z ∈ S := by
    refine ⟨?_, by simp [z]⟩
    exact hp.nonneg
  obtain ⟨q₀, -, hq₀S, hq₀max⟩ := zorn_le_nonempty₀ S (fun c hcS hc q hqc ↦ by
    have hnon : c.Nonempty := ⟨q, hqc⟩
    obtain ⟨r, hr⟩ := hcomplete c hnon hc
    have hfc := hf hc hnon hc.directedOn hr
    have hgc := hg hc hnon hc.directedOn hr
    refine ⟨r, ⟨hr.2 fun q hq ↦ (hcS hq).1, hgc.2 ?_⟩, hr.1⟩
    rintro _ ⟨q, hqc, rfl⟩
    exact (hcS hqc).2.trans (hfc.1 ⟨q, hqc, rfl⟩)) z hz
  have hq₀p : q₀.1 ≤ p := hq₀S.1
  have hq₀_ne_p : q₀.1 ≠ p := fun h ↦
    (not_le_of_gt hfg) <| by simpa [h] using hq₀S.2
  let p₁ : M := p - q₀.1
  have hp₁ : IsStarProjection p₁ := (q₀.2.le_iff_sub hp).mp hq₀p
  have hp₁_ne : p₁ ≠ 0 := sub_ne_zero.mpr hq₀_ne_p.symm
  refine ⟨p₁, hp₁, hp₁_ne, sub_le_self _ q₀.2.nonneg, ?_⟩
  intro q hq hq_ne hqp₁
  by_contra hlt
  have hq₀_mul_p₁ : q₀.1 * p₁ = 0 := by
    change q₀.1 * (p - q₀.1) = 0
    rw [mul_sub, q₀.2.le_iff_mul_eq_left hp |>.mp hq₀p,
      q₀.2.isIdempotentElem.eq, sub_self]
  have hp₁_mul_q : p₁ * q = q := hq.le_iff_mul_eq_right hp₁ |>.mp hqp₁
  have hq₀_mul_q : q₀.1 * q = 0 := by
    rw [← hp₁_mul_q, ← mul_assoc, hq₀_mul_p₁, zero_mul]
  let r : {q : M // IsStarProjection q} := ⟨q₀.1 + q, q₀.2.add hq hq₀_mul_q⟩
  have hrp : r ≤ p' := by
    change q₀.1 + q ≤ p
    rw [add_comm]
    exact (le_sub_iff_add_le).mp hqp₁
  have hrS : r ∈ S := ⟨hrp, by
    change g (q₀.1 + q) ≤ f (q₀.1 + q)
    simpa only [map_add] using add_le_add hq₀S.2 (le_of_not_lt_apply f g hq.nonneg hlt)⟩
  have hq₀r : q₀ ≤ r := by
    exact le_add_of_nonneg_right hq.nonneg
  have hrq₀ : r ≤ q₀ := hq₀max hrS hq₀r
  apply hq_ne
  apply add_left_cancel (a := q₀.1)
  simpa only [add_zero, r] using congrArg Subtype.val (hq₀r.antisymm hrq₀).symm

namespace IsNormalOnProjections

/-- If two normal positive functionals satisfy a strict inequality on a projection, then the same
strict inequality holds on every nonzero subprojection of some nonzero subprojection, provided
every nonempty chain of projections has a least upper bound. -/
theorem exists_nonzero_subprojection_lt_of_chain_lubs {f g : M →ₚ[ℂ] ℂ}
    (hf : f.IsNormalOnProjections) (hg : g.IsNormalOnProjections)
    (hcomplete : ∀ s : Set {q : M // IsStarProjection q}, s.Nonempty →
      IsChain (· ≤ ·) s → ∃ p, IsLUB s p) {p : M}
    (hp : IsStarProjection p) (hfg : f p < g p) :
    ∃ p₁ : M, IsStarProjection p₁ ∧ p₁ ≠ 0 ∧ p₁ ≤ p ∧
      ∀ {q : M}, IsStarProjection q → q ≠ 0 → q ≤ p₁ → f q < g q :=
  PositiveLinearMap.exists_nonzero_subprojection_lt_of_scottContinuousOn_chains
    hf.scottContinuousOn hg.scottContinuousOn hcomplete hp hfg

/-- A directed-complete wrapper for `exists_nonzero_subprojection_lt_of_chain_lubs`.

This preserves the previous API for callers which naturally have least upper bounds of all
nonempty directed sets of projections. -/
theorem exists_nonzero_subprojection_lt {f g : M →ₚ[ℂ] ℂ}
    (hf : f.IsNormalOnProjections) (hg : g.IsNormalOnProjections)
    (hcomplete : ∀ s : Set {q : M // IsStarProjection q}, s.Nonempty →
      DirectedOn (· ≤ ·) s → ∃ p, IsLUB s p) {p : M}
    (hp : IsStarProjection p) (hfg : f p < g p) :
    ∃ p₁ : M, IsStarProjection p₁ ∧ p₁ ≠ 0 ∧ p₁ ≤ p ∧
      ∀ {q : M}, IsStarProjection q → q ≠ 0 → q ≤ p₁ → f q < g q :=
  hf.exists_nonzero_subprojection_lt_of_chain_lubs hg
    (fun s hnon hs ↦ hcomplete s hnon hs.directedOn) hp hfg

end IsNormalOnProjections

end ChainCompleteProjectionOrder

namespace IsNormalOnProjections

section Predual

variable {M P : Type*} [NonUnitalCStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]

include P

/-- The projection-selection lemma for a non-unital C-star algebra with a specified Banach predual.

This is a convenience wrapper around `exists_nonzero_subprojection_lt`; the predual is used only
to supply the complete lattice of projections. -/
theorem exists_nonzero_subprojection_lt_of_predual {f g : M →ₚ[ℂ] ℂ}
    (hf : f.IsNormalOnProjections) (hg : g.IsNormalOnProjections) {p : M}
    (hp : IsStarProjection p) (hfg : f p < g p) :
    ∃ p₁ : M, IsStarProjection p₁ ∧ p₁ ≠ 0 ∧ p₁ ≤ p ∧
      ∀ {q : M}, IsStarProjection q → q ≠ 0 → q ≤ p₁ → f q < g q := by
  letI : IsUnital M := CStarAlgebra.isUnital_of_predual (P := P)
  letI : CStarAlgebra M := IsUnital.toCStarAlgebra
  letI : CompleteLattice {q : M // IsStarProjection q} :=
    IsStarProjection.completeLatticeOfPredual (P := P)
  exact hf.exists_nonzero_subprojection_lt hg
    (fun s _ _ ↦ ⟨sSup s, isLUB_sSup s⟩) hp hfg

end Predual

end IsNormalOnProjections

end PositiveLinearMap
