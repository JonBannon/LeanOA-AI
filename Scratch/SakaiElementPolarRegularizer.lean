import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Scratch: Sakai's element-polar-decomposition regularizer

This file checks the norm-topological part of the regularization in Sakai, Theorem 1.12.1
(printed pages 27--28).  Sakai indexes by positive integers and uses `1 / n`; here the sequence is
reindexed over Lean's naturals with `epsilon n = 1 / (n + 1)`.

The declarations remain in `Scratch`: they are proof-local evidence for the later W*-algebra
compactness argument, not a proposed public API.
-/

open Filter
open scoped Topology

namespace Scratch.SakaiElementPolarRegularizer

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

noncomputable section

/-- Sakai's positive regularization parameter, reindexed over `Nat`. -/
def epsilon (n : ℕ) : ℝ := ((n + 1 : ℝ)⁻¹)

/-- The strictly positive regularization of `star a * a`. -/
def c (a : M) (n : ℕ) : M := star a * a + epsilon n • (1 : M)

/-- The positive square root of the regularized modulus square. -/
def h (a : M) (n : ℕ) : M := CFC.sqrt (c a n)

/-- Sakai's contractive regularizer for `a`. -/
def aReg (a : M) (n : ℕ) : M := a * (c a n) ^ (-(1 / 2 : ℝ))

lemma epsilon_pos (n : ℕ) : 0 < epsilon n := by
  exact inv_pos.mpr (by positivity)

lemma epsilon_tendsto_zero : Tendsto epsilon atTop (nhds 0) := by
  change Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) atTop (nhds 0)
  simpa [one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

lemma modulusSq_nonneg (a : M) : 0 ≤ star a * a := by
  exact _root_.star_mul_self_nonneg a

lemma c_nonneg (a : M) (n : ℕ) : 0 ≤ c a n := by
  exact add_nonneg (modulusSq_nonneg a)
    (smul_nonneg (epsilon_pos n).le zero_le_one)

lemma c_strictlyPositive (a : M) (n : ℕ) : IsStrictlyPositive (c a n) := by
  exact IsStrictlyPositive.nonneg_add
    (modulusSq_nonneg a)
    (IsStrictlyPositive.smul (epsilon_pos n) isStrictlyPositive_one)

lemma star_aReg_mul_aReg (a : M) (n : ℕ) :
    star (aReg a n) * aReg a n =
      (c a n) ^ (-(1 / 2 : ℝ)) * (star a * a) *
        (c a n) ^ (-(1 / 2 : ℝ)) := by
  have hr : IsSelfAdjoint ((c a n) ^ (-(1 / 2 : ℝ))) :=
    (CFC.rpow_nonneg (a := c a n) (y := (-(1 / 2 : ℝ)))).isSelfAdjoint
  rw [aReg, star_mul, hr.star_eq]
  noncomm_ring

lemma norm_aReg_le_one (a : M) (n : ℕ) : ‖aReg a n‖ ≤ 1 := by
  have hle : star a * a ≤ c a n := by
    simp only [c]
    exact le_add_of_nonneg_right (smul_nonneg (epsilon_pos n).le zero_le_one)
  have hsqrt :
      ‖CFC.sqrt (star a * a) * (c a n) ^ (-(1 / 2 : ℝ))‖ ≤ 1 :=
    (le_iff_norm_sqrt_mul_rpow (star a * a) (c a n)
      (modulusSq_nonneg a) (c_strictlyPositive a n)).mp hle
  have hnorm :
      ‖aReg a n‖ =
        ‖CFC.sqrt (star a * a) * (c a n) ^ (-(1 / 2 : ℝ))‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    let r : M := (c a n) ^ (-(1 / 2 : ℝ))
    have hr : IsSelfAdjoint ((c a n) ^ (-(1 / 2 : ℝ))) :=
      (CFC.rpow_nonneg (a := c a n) (y := (-(1 / 2 : ℝ)))).isSelfAdjoint
    have hs : IsSelfAdjoint (CFC.sqrt (star a * a)) :=
      (CFC.sqrt_nonneg (star a * a)).isSelfAdjoint
    calc
      ‖aReg a n‖ ^ 2 = ‖star (aReg a n) * aReg a n‖ :=
        by simpa [pow_two] using
          (CStarRing.norm_star_mul_self (x := aReg a n)).symm
      _ = ‖r * (star a * a) * r‖ := by
        exact congrArg norm (star_aReg_mul_aReg a n)
      _ = ‖r * CFC.sqrt (star a * a) *
        (CFC.sqrt (star a * a) * r)‖ := by
        congr 1
        nth_rw 1 [← CFC.sqrt_mul_sqrt_self (star a * a) (modulusSq_nonneg a)]
        noncomm_ring
      _ = ‖star (CFC.sqrt (star a * a) * r) *
          (CFC.sqrt (star a * a) * r)‖ := by
        congr 1
        dsimp [r]
        rw [star_mul, hr.star_eq, hs.star_eq]
      _ = ‖CFC.sqrt (star a * a) * r‖ ^ 2 := by
        simpa [pow_two] using
          (CStarRing.norm_star_mul_self
            (x := CFC.sqrt (star a * a) * r))
  rwa [hnorm]

/-- The precise boundedness form consumed by ultraweak compactness of the closed unit ball. -/
lemma aReg_mem_unitClosedBall (a : M) (n : ℕ) :
    aReg a n ∈ Metric.closedBall (0 : M) 1 := by
  simpa [Metric.mem_closedBall, dist_zero_right] using norm_aReg_le_one a n

lemma aReg_mul_h (a : M) (n : ℕ) : aReg a n * h a n = a := by
  rw [aReg, h, CFC.sqrt_eq_rpow, mul_assoc, ← CFC.rpow_add (c_strictlyPositive a n).isUnit]
  norm_num
  rw [CFC.rpow_zero (c a n) (c_nonneg a n), mul_one]

omit [PartialOrder M] [StarOrderedRing M] in
lemma c_tendsto_star_mul_self (a : M) :
    Tendsto (c a) atTop (nhds (star a * a)) := by
  have hscalar : Tendsto (fun n : ℕ ↦ epsilon n • (1 : M)) atTop (nhds 0) := by
    simpa using epsilon_tendsto_zero.smul_const (1 : M)
  change Tendsto (fun n : ℕ ↦ star a * a + epsilon n • (1 : M)) atTop
    (nhds (star a * a))
  simpa using ((tendsto_const_nhds (x := star a * a)).add hscalar)

lemma h_tendsto_abs (a : M) : Tendsto (h a) atTop (nhds (CFC.abs a)) := by
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

lemma aReg_mul_abs_tendsto (a : M) :
    Tendsto (fun n ↦ aReg a n * CFC.abs a) atTop (nhds a) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have herr : Tendsto (fun n ↦ ‖CFC.abs a - h a n‖) atTop (nhds 0) := by
    simpa using
      ((tendsto_const_nhds (x := CFC.abs a)).sub (h_tendsto_abs a)).norm
  apply squeeze_zero (fun n ↦ norm_nonneg _)
    (fun n ↦ ?_) herr
  calc
    ‖aReg a n * CFC.abs a - a‖ =
        ‖aReg a n * (CFC.abs a - h a n)‖ := by
          rw [mul_sub, aReg_mul_h]
    _ ≤ ‖aReg a n‖ * ‖CFC.abs a - h a n‖ := norm_mul_le _ _
    _ ≤ 1 * ‖CFC.abs a - h a n‖ := by
      exact mul_le_mul_of_nonneg_right (norm_aReg_le_one a n) (norm_nonneg _)
    _ = ‖CFC.abs a - h a n‖ := one_mul _

end

end Scratch.SakaiElementPolarRegularizer
