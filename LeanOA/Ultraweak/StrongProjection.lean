module

public import LeanOA.Ultraweak.ProjectionLattice
public import LeanOA.Ultraweak.Strong

@[expose] public section

/-!
# Strong convergence of projections

This file connects the intrinsic strong topology of a dual C-star algebra with its projection
lattice.  For projections dominated by the limiting projection, ultraweak convergence upgrades to
strong convergence.  Consequently, the canonical net of a directed family of projections
converges strongly to its least upper bound.
-/

open Filter Set
open scoped ComplexOrder Topology Ultraweak

namespace Ultraweak.Strong

variable {M P I : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup P] [NormedSpace ℂ P] [Predual ℂ M P]

/-- A net of projections dominated by its limiting projection converges strongly whenever it
converges ultraweakly. -/
theorem tendsto_of_tendsto_toUltraweak_of_eventually_le
    {l : Filter I} (p : I → {p : M // IsStarProjection p})
    (q : {p : M // IsStarProjection p})
    (hpq : ∀ᶠ i in l, p i ≤ q)
    (huw : Tendsto (fun i ↦ toUltraweak ℂ P (p i).1) l
      (nhds (toUltraweak ℂ P q.1))) :
    Tendsto (fun i ↦ toStrong P (p i).1) l (nhds (toStrong P q.1)) := by
  rw [withSeminorms.tendsto_nhds]
  intro phi ε hε
  have hsub : Tendsto (fun i ↦ toUltraweak ℂ P (q.1 - (p i).1)) l
      (nhds (toUltraweak ℂ P 0)) := by
    simpa only [toUltraweak_sub, toUltraweak_zero, sub_self] using
      ((tendsto_const_nhds : Tendsto (fun _ : I ↦ toUltraweak ℂ P q.1) l
        (nhds (toUltraweak ℂ P q.1))).sub huw)
  have hphi : Tendsto (fun i ↦ phi (toUltraweak ℂ P (q.1 - (p i).1))) l
      (nhds 0) := by
    convert phi.continuous.continuousAt.tendsto.comp hsub using 1 <;>
      simp [Function.comp_def]
  have hsqrt : Tendsto (fun i ↦ √‖phi (toUltraweak ℂ P (q.1 - (p i).1))‖) l
      (nhds 0) := by
    convert (Real.continuous_sqrt.comp continuous_norm).continuousAt.tendsto.comp hphi using 1 <;>
      simp [Function.comp_def]
  filter_upwards [hpq, hsqrt.eventually (Iio_mem_nhds hε)] with i hi hsmall
  rw [seminormFamily, seminorm_apply]
  have hd : IsStarProjection (q.1 - (p i).1) :=
    ((p i).2.le_iff_sub q.2).mp hi
  have hsq : star ((p i).1 - q.1) * ((p i).1 - q.1) = q.1 - (p i).1 := by
    rw [show (p i).1 - q.1 = -(q.1 - (p i).1) by abel, star_neg,
      hd.isSelfAdjoint.star_eq, neg_mul, mul_neg, neg_neg, hd.isIdempotentElem.eq]
  change √‖phi (toUltraweak ℂ P (star ((p i).1 - q.1) * ((p i).1 - q.1)))‖ < ε
  rw [hsq]
  exact hsmall

/-- For three nested projections, the strong seminorm of the middle-minus-largest difference is at
most the seminorm of the smallest-minus-largest difference. -/
theorem seminorm_sub_le_of_le
    (phi : σ(M, P) →P[ℂ] ℂ)
    (p q r : {p : M // IsStarProjection p}) (hpq : p ≤ q) (hqr : q ≤ r) :
    seminorm phi (toStrong P q.1 - toStrong P r.1) ≤
      seminorm phi (toStrong P p.1 - toStrong P r.1) := by
  rw [seminorm_apply, seminorm_apply]
  have hdq : IsStarProjection (r.1 - q.1) := (q.2.le_iff_sub r.2).mp hqr
  have hdp : IsStarProjection (r.1 - p.1) := (p.2.le_iff_sub r.2).mp (hpq.trans hqr)
  have hsq (a : {p : M // IsStarProjection p}) (ha : a ≤ r)
      (hd : IsStarProjection (r.1 - a.1)) :
      star (a.1 - r.1) * (a.1 - r.1) = r.1 - a.1 := by
    rw [show a.1 - r.1 = -(r.1 - a.1) by abel, star_neg,
      hd.isSelfAdjoint.star_eq, neg_mul, mul_neg, neg_neg, hd.isIdempotentElem.eq]
  change √‖phi (toUltraweak ℂ P (star (q.1 - r.1) * (q.1 - r.1)))‖ ≤
    √‖phi (toUltraweak ℂ P (star (p.1 - r.1) * (p.1 - r.1)))‖
  rw [hsq q hqr hdq, hsq p (hpq.trans hqr) hdp]
  gcongr
  have hqpos : 0 ≤ phi (toUltraweak ℂ P (r.1 - q.1)) := by
    simpa using OrderHomClass.mono phi
      (Ultraweak.monotone_toUltraweak (P := P) hdq.nonneg)
  have hle : phi (toUltraweak ℂ P (r.1 - q.1)) ≤
      phi (toUltraweak ℂ P (r.1 - p.1)) := by
    apply phi.mono
    apply Ultraweak.monotone_toUltraweak (P := P)
    exact sub_le_sub_left (show p.1 ≤ q.1 from hpq) r.1
  exact CStarAlgebra.norm_le_norm_of_nonneg_of_le hqpos hle

variable [CompleteSpace P]

/-- The canonical net of a nonempty directed family of projections converges strongly to any
specified least upper bound in the projection order. -/
theorem tendsto_toStrong_of_isLUB
    (s : Set {p : M // IsStarProjection p})
    (hs : DirectedOn (· ≤ ·) s) (hnon : s.Nonempty) {p : {p : M // IsStarProjection p}}
    (hp : IsLUB s p) :
    Tendsto (fun q : s ↦ toStrong P q.1.1) atTop (nhds (toStrong P p.1)) := by
  apply tendsto_of_tendsto_toUltraweak_of_eventually_le
  · exact Eventually.of_forall fun q ↦ hp.1 q.2
  · exact IsStarProjection.tendsto_toUltraweak_of_isLUB s hs hnon hp

end Ultraweak.Strong
