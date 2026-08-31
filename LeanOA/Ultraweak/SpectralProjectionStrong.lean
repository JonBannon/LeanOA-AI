module

public import LeanOA.Ultraweak.SpectralProjection
public import LeanOA.Ultraweak.StrongProjection

@[expose] public section

/-!
# Strong continuity of lower spectral projections

This file proves continuity from below for the lower spectral projections of a self-adjoint
element in the intrinsic strong topology associated to a specified predual.  The filter-level
theorem does not assume monotonicity; its sequential specialization is Sakai, Lemma 1.11.1.
-/

open Filter Set
open scoped Topology Ultraweak

namespace WStarAlgebra

variable {M P I : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [WStarAlgebra M] [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P]
  [Predual ℂ M P]

/-- An increasing net of lower spectral projections converges in the intrinsic strong topology
when its cuts converge. -/
theorem tendsto_spectralProjectionIio_strong_of_monotone
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (a : selfAdjoint M) {f : I → ℝ} {r : ℝ} (hf : Monotone f)
    (hfr : Tendsto f atTop (nhds r)) :
    Tendsto (fun i ↦ Ultraweak.toStrong P (spectralProjectionIio a (f i)).1) atTop
      (nhds (Ultraweak.toStrong P (spectralProjectionIio a r).1)) := by
  apply Ultraweak.Strong.tendsto_of_tendsto_toUltraweak_of_eventually_le
  · exact Eventually.of_forall fun i ↦
      spectralProjectionIio_mono a (hf.ge_of_tendsto hfr i)
  · exact tendsto_spectralProjectionIio_of_monotone a hf hfr

/-- Lower spectral projections converge strongly whenever their cuts converge to `r` from below.

This filter formulation is more general than Sakai, Lemma 1.11.1: it requires only eventual
domination by `r` and does not assume that the cuts are monotone. -/
theorem tendsto_spectralProjectionIio_strong_of_tendsto_of_eventually_le
    (a : selfAdjoint M) {l : Filter I} {f : I → ℝ} {r : ℝ}
    (hfr : Tendsto f l (nhds r)) (hbelow : ∀ᶠ i in l, f i ≤ r) :
    Tendsto (fun i ↦ Ultraweak.toStrong P (spectralProjectionIio a (f i)).1) l
      (nhds (Ultraweak.toStrong P (spectralProjectionIio a r).1)) := by
  obtain ⟨g, hgmono, hgr, hgto⟩ := exists_seq_strictMono_tendsto r
  have hgStrong := tendsto_spectralProjectionIio_strong_of_monotone
    (P := P) a hgmono.monotone hgto
  rw [Ultraweak.Strong.withSeminorms.tendsto_nhds] at hgStrong ⊢
  intro phi ε hε
  obtain ⟨n, hn⟩ := (hgStrong phi ε hε).exists
  have hlower : ∀ᶠ i in l, g n ≤ f i := hfr.eventually (Ici_mem_nhds (hgr n))
  filter_upwards [hlower, hbelow] with i hgi hir
  exact (Ultraweak.Strong.seminorm_sub_le_of_le phi
    (spectralProjectionIio a (g n)) (spectralProjectionIio a (f i))
    (spectralProjectionIio a r)
    (spectralProjectionIio_mono a hgi) (spectralProjectionIio_mono a hir)).trans_lt hn

/-- The lower spectral projection family is strongly continuous from the left at every cut. -/
theorem continuousWithinAt_spectralProjectionIio_strong
    (a : selfAdjoint M) (r : ℝ) :
    ContinuousWithinAt
      (fun t ↦ Ultraweak.toStrong P (spectralProjectionIio a t).1) (Iic r) r := by
  apply tendsto_spectralProjectionIio_strong_of_tendsto_of_eventually_le
  · exact tendsto_id.mono_left inf_le_left
  · exact mem_of_superset self_mem_nhdsWithin fun _ ↦ id

/-- **Sakai, Lemma 1.11.1.** If `f n ≤ r` for every `n` and `f n → r`, then the
lower spectral projections at `f n` converge to the lower spectral projection at `r` in
`s(M, P)`.  No monotonicity hypothesis on `f` is required. -/
theorem tendsto_spectralProjectionIio_strong
    (a : selfAdjoint M) {f : ℕ → ℝ} {r : ℝ}
    (hbelow : ∀ n, f n ≤ r) (hfr : Tendsto f atTop (nhds r)) :
    Tendsto (fun n ↦ Ultraweak.toStrong P (spectralProjectionIio a (f n)).1) atTop
      (nhds (Ultraweak.toStrong P (spectralProjectionIio a r).1)) :=
  tendsto_spectralProjectionIio_strong_of_tendsto_of_eventually_le
    (P := P) a hfr (Eventually.of_forall hbelow)

end WStarAlgebra
