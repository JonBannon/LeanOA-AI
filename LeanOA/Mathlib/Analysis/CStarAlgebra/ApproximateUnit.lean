module

public import Mathlib.Analysis.CStarAlgebra.ApproximateUnit

@[expose] public section

open CStarAlgebra Topology Filter
open scoped Topology

section ApproximateUnit

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]

instance [StarOrderedRing A] : (approximateUnit A).NeBot := (increasingApproximateUnit A).neBot

namespace Filter.IsIncreasingApproximateUnit

lemma nonneg_mem {l : Filter A} (hl : l.IsIncreasingApproximateUnit) :
    {x | 0 ≤ x} ∈ l := by
  simpa using! hl.eventually_nonneg

/-- An increasing approximate-unit filter contains a sequence of positive contractions which is
a right approximate unit for any prescribed element. The same sequence remains a right
approximate unit after squaring. -/
lemma exists_seq_tendsto_mul_left_sq {l : Filter A}
    (hl : l.IsIncreasingApproximateUnit) (a : A) :
    ∃ e : ℕ → A, (∀ n, 0 ≤ e n ∧ ‖e n‖ ≤ 1) ∧
      Tendsto (fun n ↦ a * e n) atTop (nhds a) ∧
      Tendsto (fun n ↦ a * (e n * e n)) atTop (nhds a) := by
  letI := hl.neBot
  choose e he using fun n : ℕ ↦ (hl.eventually_nonneg.and <| hl.eventually_norm.and <|
    (hl.tendsto_mul_left a).eventually <|
      Metric.ball_mem_nhds a
        (show 0 < 1 / ((n : ℝ) + 1) from one_div_pos.mpr <| by positivity)).exists
  refine ⟨e, fun n ↦ ⟨(he n).1, (he n).2.1⟩, ?_, ?_⟩
  · rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp <|
      tendsto_one_div_add_atTop_nhds_zero_nat.eventually <| Iio_mem_nhds hε
    exact ⟨N, fun n hn ↦ (he n).2.2.trans <| hN n hn⟩
  · rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp <|
      tendsto_one_div_add_atTop_nhds_zero_nat.eventually <| Iio_mem_nhds (half_pos hε)
    refine ⟨N, fun n hn ↦ ?_⟩
    have hn' := hN n hn
    rw [dist_eq_norm]
    calc
      ‖a * (e n * e n) - a‖ = ‖(a * e n - a) * e n + (a * e n - a)‖ := by
        congr 1
        noncomm_ring
      _ ≤ ‖a * e n - a‖ * ‖e n‖ + ‖a * e n - a‖ :=
        norm_add_le _ _ |>.trans <| add_le_add (norm_mul_le _ _) le_rfl
      _ ≤ 2 * ‖a * e n - a‖ := by
        calc
          _ ≤ ‖a * e n - a‖ * 1 + ‖a * e n - a‖ :=
            add_le_add (mul_le_mul_of_nonneg_left (he n).2.1 <| norm_nonneg _) le_rfl
          _ = _ := by ring
      _ < ε := by
        have haen : ‖a * e n - a‖ < 1 / ((n : ℝ) + 1) := by
          simpa [dist_eq_norm] using (he n).2.2
        linarith

end Filter.IsIncreasingApproximateUnit

namespace CStarAlgebra

/-- Every element of a nonunital C⋆-algebra admits a sequential positive contractive right
approximate unit, which remains an approximate unit after squaring. -/
lemma exists_seq_tendsto_mul_left_sq [StarOrderedRing A] (a : A) :
    ∃ e : ℕ → A, (∀ n, 0 ≤ e n ∧ ‖e n‖ ≤ 1) ∧
      Tendsto (fun n ↦ a * e n) atTop (nhds a) ∧
      Tendsto (fun n ↦ a * (e n * e n)) atTop (nhds a) :=
  (increasingApproximateUnit A).exists_seq_tendsto_mul_left_sq a

end CStarAlgebra

end ApproximateUnit
