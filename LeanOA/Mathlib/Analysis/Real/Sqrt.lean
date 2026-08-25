module

public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

open Filter Topology

lemma Real.tendsto_sqrt_one_add_sq_sub_self_atTop :
    Tendsto (fun x : ℝ ↦ √(1 + x ^ 2) - x) atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ ↦ (√(1 + x ^ 2) + x)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp <|
      tendsto_atTop_mono (fun x ↦ le_add_of_nonneg_left (Real.sqrt_nonneg _)) tendsto_id
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [inv_eq_one_div, div_eq_iff (by positivity)]
  nlinarith [Real.sq_sqrt (by positivity : 0 ≤ 1 + x ^ 2)]
