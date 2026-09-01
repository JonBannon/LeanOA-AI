module

public import LeanOA.Ultraweak.AbsSupport

import LeanOA.Ultraweak.Multiplication
import LeanOA.Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-!
# Polar decomposition of elements of a von Neumann algebra

This file proves the existence part of Sakai, Theorem 1.12.1.  The implementation follows
Sakai's regularization and ultraweak-compactness argument, while keeping the regularizer itself
private.
-/

open Filter
open scoped Topology Ultraweak

namespace WStarAlgebra

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

noncomputable section

namespace ElementPolarDecomposition

private def epsilon (n : ℕ) : ℝ := ((n + 1 : ℝ)⁻¹)

private def c (a : M) (n : ℕ) : M := star a * a + epsilon n • (1 : M)

private def h (a : M) (n : ℕ) : M := CFC.sqrt (c a n)

private def regularizer (a : M) (n : ℕ) : M :=
  a * (c a n) ^ (-(1 / 2 : ℝ))

private lemma epsilon_pos (n : ℕ) : 0 < epsilon n := by
  exact inv_pos.mpr (by positivity)

private lemma epsilon_tendsto_zero : Tendsto epsilon atTop (nhds 0) := by
  change Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) atTop (nhds 0)
  simpa [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)

private lemma modulusSq_nonneg (a : M) : 0 ≤ star a * a :=
  _root_.star_mul_self_nonneg a

private lemma c_nonneg (a : M) (n : ℕ) : 0 ≤ c a n := by
  exact add_nonneg (modulusSq_nonneg a)
    (smul_nonneg (epsilon_pos n).le zero_le_one)

private lemma c_strictlyPositive (a : M) (n : ℕ) : IsStrictlyPositive (c a n) := by
  exact IsStrictlyPositive.nonneg_add
    (modulusSq_nonneg a)
    (IsStrictlyPositive.smul (epsilon_pos n) isStrictlyPositive_one)

private lemma star_regularizer_mul_regularizer (a : M) (n : ℕ) :
    star (regularizer a n) * regularizer a n =
      (c a n) ^ (-(1 / 2 : ℝ)) * (star a * a) *
        (c a n) ^ (-(1 / 2 : ℝ)) := by
  have hr : IsSelfAdjoint ((c a n) ^ (-(1 / 2 : ℝ))) :=
    (CFC.rpow_nonneg (a := c a n) (y := (-(1 / 2 : ℝ)))).isSelfAdjoint
  rw [regularizer, star_mul, hr.star_eq]
  noncomm_ring

private lemma norm_regularizer_le_one (a : M) (n : ℕ) : ‖regularizer a n‖ ≤ 1 := by
  have hle : star a * a ≤ c a n := by
    exact le_add_of_nonneg_right (smul_nonneg (epsilon_pos n).le zero_le_one)
  have hsqrt :
      ‖CFC.sqrt (star a * a) * (c a n) ^ (-(1 / 2 : ℝ))‖ ≤ 1 :=
    (le_iff_norm_sqrt_mul_rpow (star a * a) (c a n)
      (modulusSq_nonneg a) (c_strictlyPositive a n)).mp hle
  have hnorm :
      ‖regularizer a n‖ =
        ‖CFC.sqrt (star a * a) * (c a n) ^ (-(1 / 2 : ℝ))‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    let r : M := (c a n) ^ (-(1 / 2 : ℝ))
    have hr : IsSelfAdjoint r :=
      (CFC.rpow_nonneg (a := c a n) (y := (-(1 / 2 : ℝ)))).isSelfAdjoint
    have hs : IsSelfAdjoint (CFC.sqrt (star a * a)) :=
      (CFC.sqrt_nonneg (star a * a)).isSelfAdjoint
    calc
      ‖regularizer a n‖ ^ 2 = ‖star (regularizer a n) * regularizer a n‖ :=
        by simpa [pow_two] using
          (CStarRing.norm_star_mul_self (x := regularizer a n)).symm
      _ = ‖r * (star a * a) * r‖ := by
        exact congrArg norm (star_regularizer_mul_regularizer a n)
      _ = ‖r * CFC.sqrt (star a * a) *
          (CFC.sqrt (star a * a) * r)‖ := by
        congr 1
        nth_rw 1 [← CFC.sqrt_mul_sqrt_self (star a * a) (modulusSq_nonneg a)]
        noncomm_ring
      _ = ‖star (CFC.sqrt (star a * a) * r) *
          (CFC.sqrt (star a * a) * r)‖ := by
        congr 1
        rw [star_mul, hr.star_eq, hs.star_eq]
      _ = ‖CFC.sqrt (star a * a) * r‖ ^ 2 := by
        simpa [pow_two] using
          (CStarRing.norm_star_mul_self
            (x := CFC.sqrt (star a * a) * r))
  rwa [hnorm]

private lemma regularizer_mem_unitClosedBall (a : M) (n : ℕ) :
    regularizer a n ∈ Metric.closedBall (0 : M) 1 := by
  simpa [Metric.mem_closedBall, dist_zero_right] using norm_regularizer_le_one a n

private lemma regularizer_mul_h (a : M) (n : ℕ) : regularizer a n * h a n = a := by
  rw [regularizer, h, CFC.sqrt_eq_rpow, mul_assoc,
    ← CFC.rpow_add (c_strictlyPositive a n).isUnit]
  norm_num
  rw [CFC.rpow_zero (c a n) (c_nonneg a n), mul_one]

omit [PartialOrder M] [StarOrderedRing M] in
private lemma c_tendsto_star_mul_self (a : M) :
    Tendsto (c a) atTop (nhds (star a * a)) := by
  have hscalar : Tendsto (fun n : ℕ ↦ epsilon n • (1 : M)) atTop (nhds 0) := by
    simpa using epsilon_tendsto_zero.smul_const (1 : M)
  change Tendsto (fun n : ℕ ↦ star a * a + epsilon n • (1 : M)) atTop
    (nhds (star a * a))
  simpa using (tendsto_const_nhds.add hscalar)

private lemma h_tendsto_abs (a : M) : Tendsto (h a) atTop (nhds (CFC.abs a)) := by
  have hcWithin :
      Tendsto (c a) atTop (nhdsWithin (star a * a) {x : M | 0 ≤ x}) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨c_tendsto_star_mul_self a, Eventually.of_forall (c_nonneg a)⟩
  have hsqrtWithin :
      ContinuousWithinAt CFC.sqrt {x : M | 0 ≤ x} (star a * a) :=
    CFC.continuousOn_sqrt (star a * a) (modulusSq_nonneg a)
  have hlim := hsqrtWithin.tendsto.comp hcWithin
  change Tendsto (fun n ↦ CFC.sqrt (c a n)) atTop
    (nhds (CFC.sqrt (star a * a)))
  simpa [Function.comp_def] using hlim

private lemma regularizer_mul_abs_tendsto (a : M) :
    Tendsto (fun n ↦ regularizer a n * CFC.abs a) atTop (nhds a) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have herr : Tendsto (fun n ↦ ‖CFC.abs a - h a n‖) atTop (nhds 0) := by
    simpa using
      (((tendsto_const_nhds (x := CFC.abs a)).sub (h_tendsto_abs a)).norm)
  apply squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_) herr
  calc
    ‖regularizer a n * CFC.abs a - a‖ =
        ‖regularizer a n * (CFC.abs a - h a n)‖ := by
          rw [mul_sub, regularizer_mul_h]
    _ ≤ ‖regularizer a n‖ * ‖CFC.abs a - h a n‖ := norm_mul_le _ _
    _ ≤ 1 * ‖CFC.abs a - h a n‖ := by
      exact mul_le_mul_of_nonneg_right (norm_regularizer_le_one a n) (norm_nonneg _)
    _ = ‖CFC.abs a - h a n‖ := one_mul _

section WStar

variable [WStarAlgebra M]

/-- Sakai's compactness handoff: a contractive ultraweak cluster point still factors `a`
through its absolute value. -/
private theorem exists_contractive_factor (a : M) :
    ∃ b : M, ‖b‖ ≤ 1 ∧ b * CFC.abs a = a := by
  let P := WStarAlgebra.predual M
  let f : ℕ → σ(M, P) := fun n ↦ toUltraweak ℂ P (regularizer a n)
  have hmap : map f atTop ≤
      𝓟 (ofUltraweak ⁻¹' Metric.closedBall (0 : M) 1) := by
    simp only [le_principal_iff, mem_map]
    exact Eventually.of_forall fun n ↦ by
      simpa [f] using regularizer_mem_unitClosedBall a n
  obtain ⟨bσ, hbσ, hbcluster⟩ :=
    (Ultraweak.isCompact_closedBall ℂ P (0 : M) 1).exists_mapClusterPt hmap
  let b : M := ofUltraweak bσ
  have hbnorm : ‖b‖ ≤ 1 := by
    simpa [b, Metric.mem_closedBall, dist_zero_right] using hbσ
  obtain ⟨l, hl, hblim⟩ := mapClusterPt_iff_ultrafilter.mp hbcluster
  have hblim_mul :
      Tendsto (fun n ↦ toUltraweak ℂ P (regularizer a n * CFC.abs a)) l
        (nhds (toUltraweak ℂ P (b * CFC.abs a))) := by
    simpa [f, b] using hblim.mul_const (toUltraweak ℂ P (CFC.abs a))
  have halim :
      Tendsto (fun n ↦ toUltraweak ℂ P (regularizer a n * CFC.abs a)) l
        (nhds (toUltraweak ℂ P a)) := by
    exact ((continuous_toUltraweak (𝕜 := ℂ) (M := M) (P := P)).continuousAt.tendsto.comp
      (regularizer_mul_abs_tendsto a)).mono_left hl
  refine ⟨b, hbnorm, ?_⟩
  exact toUltraweak_inj.mp (tendsto_nhds_unique hblim_mul halim)

/-- Sakai's support-defect cutdown. -/
private theorem exists_support_cutdown (a b : M) (hb : ‖b‖ ≤ 1)
    (hba : b * CFC.abs a = a) :
    ∃ u : M,
      a = u * CFC.abs a ∧
      star u * u =
        (support ⟨CFC.abs a, (CFC.abs_nonneg a).isSelfAdjoint⟩).1 ∧
      u * star u = (support
        ⟨CFC.abs (star a), (CFC.abs_nonneg (star a)).isSelfAdjoint⟩).1 := by
  let x : M := CFC.abs a
  let p : {p : M // IsStarProjection p} :=
    support ⟨x, (CFC.abs_nonneg a).isSelfAdjoint⟩
  let q : {q : M // IsStarProjection q} :=
    support ⟨CFC.abs (star a), (CFC.abs_nonneg (star a)).isSelfAdjoint⟩
  let u : M := q.1 * b * p.1
  have hxstar : star x = x := by
    simpa only [x] using (CFC.abs_nonneg a).star_eq
  have hpx : p.1 * x = x :=
    support_mul ⟨x, (CFC.abs_nonneg a).isSelfAdjoint⟩
  have hxp : x * p.1 = x :=
    mul_support ⟨x, (CFC.abs_nonneg a).isSelfAdjoint⟩
  have hqa : q.1 * a = a := by
    rw [show q = leftSupport a by simp [q]]
    exact leftSupport_mul a
  have hua : u * x = a := by
    simp only [u, mul_assoc]
    rw [hpx, hba, hqa]
  have hbstarb_le_one : star b * b ≤ (1 : M) := by
    apply (CStarAlgebra.norm_le_one_iff_of_nonneg (star b * b)
      (star_mul_self_nonneg b)).mp
    rw [CStarRing.norm_star_mul_self]
    nlinarith [norm_nonneg b]
  have hbqb_le_one : star b * q.1 * b ≤ (1 : M) := by
    calc
      star b * q.1 * b ≤ star b * 1 * b :=
        star_left_conjugate_le_conjugate q.2.le_one b
      _ = star b * b := by simp
      _ ≤ 1 := hbstarb_le_one
  have hstaru : star u * u = p.1 * (star b * q.1 * b) * p.1 := by
    have hsu : star u = p.1 * star b * q.1 := by
      simp only [u, star_mul, p.2.isSelfAdjoint.star_eq,
        q.2.isSelfAdjoint.star_eq, mul_assoc]
    rw [hsu]
    simp only [u]
    calc
      (p.1 * star b * q.1) * (q.1 * b * p.1) =
          p.1 * star b * (q.1 * q.1) * b * p.1 := by noncomm_ring
      _ = p.1 * (star b * q.1 * b) * p.1 := by
        rw [q.2.isIdempotentElem.eq]
        noncomm_ring
  have hstaru_le_p : star u * u ≤ p.1 := by
    rw [hstaru]
    calc
      p.1 * (star b * q.1 * b) * p.1 ≤ p.1 * 1 * p.1 := by
        simpa only [p.2.isSelfAdjoint.star_eq] using
          star_left_conjugate_le_conjugate hbqb_le_one p.1
      _ = p.1 := by rw [mul_one, p.2.isIdempotentElem.eq]
  have hd_nonneg : 0 ≤ p.1 - star u * u := sub_nonneg.mpr hstaru_le_p
  have hd_sandwich : x * (p.1 - star u * u) * x = 0 := by
    have hstarhua : star a = x * star u := by
      have hstarhua' := congr_arg star hua
      simpa only [star_mul, hxstar] using hstarhua'.symm
    calc
      x * (p.1 - star u * u) * x = x * x - (x * star u) * (u * x) := by
        rw [mul_sub, sub_mul, hxp]
        noncomm_ring
      _ = star a * a - star a * a := by
        rw [← hstarhua, hua, CFC.abs_mul_abs]
      _ = 0 := sub_self _
  have hd_mul_x : (p.1 - star u * u) * x = 0 := by
    let d : M := p.1 - star u * u
    have hsqrt : CFC.sqrt d * x = 0 := by
      rw [← CStarRing.star_mul_self_eq_zero_iff]
      calc
        star (CFC.sqrt d * x) * (CFC.sqrt d * x) =
            x * (CFC.sqrt d * CFC.sqrt d) * x := by
          simp only [star_mul, (CFC.sqrt_nonneg d).star_eq, hxstar, mul_assoc]
        _ = x * d * x := by rw [CFC.sqrt_mul_sqrt_self d hd_nonneg]
        _ = 0 := hd_sandwich
    change d * x = 0
    rw [← CFC.sqrt_mul_sqrt_self d hd_nonneg, mul_assoc, hsqrt, mul_zero]
  have hstaru_eq_p : star u * u = p.1 := by
    have hd_mul_p : (p.1 - star u * u) * p.1 = 0 :=
      (mul_support_eq_zero_iff ⟨x, (CFC.abs_nonneg a).isSelfAdjoint⟩
        (p.1 - star u * u)).2 hd_mul_x
    have hup : u * p.1 = u := by
      simp only [u, mul_assoc, p.2.isIdempotentElem.eq]
    have hstaru_p : (star u * u) * p.1 = star u * u := by
      rw [mul_assoc, hup]
    rw [sub_mul, p.2.isIdempotentElem.eq, hstaru_p, sub_eq_zero] at hd_mul_p
    exact hd_mul_p.symm
  have hr : IsStarProjection (u * star u) :=
    (hstaru_eq_p.symm ▸ p.2).mul_star_self
  have hqu : q.1 * u = u := by
    simp only [u, ← mul_assoc, q.2.isIdempotentElem.eq]
  have hfinal_le_q :
      (⟨u * star u, hr⟩ : {r : M // IsStarProjection r}) ≤ q := by
    change u * star u ≤ q.1
    rw [hr.le_iff_mul_eq_right q.2, ← mul_assoc, hqu]
  have hq_le_final :
      q ≤ (⟨u * star u, hr⟩ : {r : M // IsStarProjection r}) := by
    rw [show q = leftSupport a by simp [q]]
    rw [leftSupport_le_iff]
    have hi : IsStarProjection (star u * u) := hstaru_eq_p.symm ▸ p.2
    rw [hua.symm, ← mul_assoc, hi.mul_star_mul_self, hua]
  have hfinal : u * star u = q.1 :=
    congr_arg Subtype.val (le_antisymm hfinal_le_q hq_le_final)
  refine ⟨u, hua.symm, hstaru_eq_p, hfinal⟩

end WStar

end ElementPolarDecomposition

variable [WStarAlgebra M]

/-- Existence in the polar decomposition of an element of a von Neumann algebra.

This is the existence half of Sakai, Theorem 1.12.1. -/
theorem exists_element_polar_decomposition (a : M) :
    ∃ u : M,
      a = u * CFC.abs a ∧
      star u * u =
        (support ⟨CFC.abs a, (CFC.abs_nonneg a).isSelfAdjoint⟩).1 ∧
      u * star u = (support
        ⟨CFC.abs (star a), (CFC.abs_nonneg (star a)).isSelfAdjoint⟩).1 := by
  obtain ⟨b, hb, hba⟩ := ElementPolarDecomposition.exists_contractive_factor a
  exact ElementPolarDecomposition.exists_support_cutdown a b hb hba

end

end WStarAlgebra
