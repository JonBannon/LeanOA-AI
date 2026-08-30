module

public import Scratch.FiniteCutEnumeration
public import Scratch.DivisionRefinementCofinality
public import Mathlib.Topology.MetricSpace.Bounded

@[expose] public section

/-!
# Scratch: a refinement, endpoint-escape, and mesh filter on finite real cuts

This file kernel-tests a candidate filter for prescribed-cut Radon--Stieltjes sums.  It is not a
claim that Sakai specified this Moore--Smith model.  The simultaneous-feasibility proof constructs
a finite metric net in a compact interval; it does not postulate compatible mesh and endpoint
conditions.
-/

open Filter Metric Set
open Scratch.FiniteCutEnumeration

namespace Scratch.RadonStieltjesMeshFilter

/-- The finite collection of lengths of adjacent bands. -/
noncomputable def adjacentGaps (d : Finset ℝ) : Finset ℝ :=
  (Finset.range (bandCount d)).image fun i ↦ orderedCut d (i + 1) - orderedCut d i

/-- The global mesh of a finite real cut set: the maximum adjacent gap, or zero if there is no
band. -/
noncomputable def divisionMesh (d : Finset ℝ) : ℝ :=
  (insert 0 (adjacentGaps d)).max' (Finset.insert_nonempty 0 _)

theorem divisionMesh_nonneg (d : Finset ℝ) : 0 ≤ divisionMesh d := by
  exact Finset.le_max' _ _ (Finset.mem_insert_self 0 _)

theorem adjacent_gap_le_divisionMesh (d : Finset ℝ) {i : ℕ} (hi : i < bandCount d) :
    orderedCut d (i + 1) - orderedCut d i ≤ divisionMesh d := by
  apply Finset.le_max'
  simp only [Finset.mem_insert, adjacentGaps, Finset.mem_image]
  exact Or.inr ⟨i, Finset.mem_range.mpr hi, rfl⟩

theorem divisionMesh_le {d : Finset ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hgap : ∀ i, i < bandCount d → orderedCut d (i + 1) - orderedCut d i ≤ c) :
    divisionMesh d ≤ c := by
  apply Finset.max'_le
  intro x hx
  simp only [Finset.mem_insert, adjacentGaps, Finset.mem_image] at hx
  rcases hx with rfl | ⟨i, hi, rfl⟩
  · exact hc
  · exact hgap i (Finset.mem_range.mp hi)

/-- No member of a finite cut set lies strictly between two canonically adjacent cuts. -/
theorem no_mem_Ioo_orderedCut_succ (d : Finset ℝ) {i : ℕ} (hi : i < bandCount d)
    {x : ℝ} (hx : x ∈ d) : x ∉ Ioo (orderedCut d i) (orderedCut d (i + 1)) := by
  rintro ⟨hix, hxi⟩
  rcases exists_index_orderedCut_eq d hx with ⟨j, hj, hjx⟩
  have hi_card : i < d.card := by
    change i < d.card - 1 at hi
    omega
  have hi1_card : i + 1 < d.card := by
    change i < d.card - 1 at hi
    omega
  have hji : i < j := by
    by_contra h
    have hle : j ≤ i := Nat.le_of_not_gt h
    have := (d.orderEmbOfFin rfl).monotone (show (⟨j, hj⟩ : Fin d.card) ≤ ⟨i, hi_card⟩ by
      simpa using hle)
    rw [← orderedCut_of_lt_card d hj, ← orderedCut_of_lt_card d hi_card, hjx] at this
    exact (not_le_of_gt hix) this
  have hj1 : i + 1 ≤ j := by omega
  have := (d.orderEmbOfFin rfl).monotone
    (show (⟨i + 1, hi1_card⟩ : Fin d.card) ≤ ⟨j, hj⟩ by simpa using hj1)
  rw [← orderedCut_of_lt_card d hi1_card, ← orderedCut_of_lt_card d hj, hjx] at this
  exact (not_le_of_gt hxi) this

/-- Every finite prescribed cut set admits a finite refinement with arbitrarily small global
mesh.  The witness is obtained by adding a finite `ε / 4`-net of the compact interval spanned by
the prescribed cuts (and `0`). -/
theorem exists_refinement_divisionMesh_lt (S : Finset ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ d : Finset ℝ, S ⊆ d ∧ divisionMesh d < ε := by
  let base : Finset ℝ := insert 0 S
  have hbase : base.Nonempty := Finset.insert_nonempty 0 S
  let a : ℝ := base.min' hbase
  let b : ℝ := base.max' hbase
  have hhalf : 0 < ε / 2 := by linarith
  have hhalf_lt : ε / 2 < ε := by linarith
  have hquarter : 0 < ε / 4 := by linarith
  obtain ⟨t, htIcc, htfinite, htcover⟩ :=
    Metric.finite_approx_of_totallyBounded (totallyBounded_Icc a b) (ε / 4) hquarter
  let net : Finset ℝ := htfinite.toFinset
  let d : Finset ℝ := base ∪ net
  have hbase_subset : base ⊆ d := Finset.subset_union_left
  have hS : S ⊆ d := (Finset.subset_insert 0 S).trans hbase_subset
  refine ⟨d, hS, lt_of_le_of_lt ?_ hhalf_lt⟩
  apply divisionMesh_le hhalf.le
  intro i hi
  have hi_card : i < d.card := by
    change i < d.card - 1 at hi
    omega
  have hi1_card : i + 1 < d.card := by
    change i < d.card - 1 at hi
    omega
  let x : ℝ := orderedCut d i
  let y : ℝ := orderedCut d (i + 1)
  have hxmem : x ∈ d := orderedCut_mem d hi_card
  have hymem : y ∈ d := orderedCut_mem d hi1_card
  have hxy : x < y := orderedCut_lt_succ d hi
  have hbase_Icc {z : ℝ} (hz : z ∈ base) : z ∈ Icc a b := by
    exact ⟨base.min'_le z hz, base.le_max' z hz⟩
  have hd_Icc {z : ℝ} (hz : z ∈ d) : z ∈ Icc a b := by
    rcases Finset.mem_union.mp hz with hz | hz
    · exact hbase_Icc hz
    · apply htIcc
      simpa only [net, Set.Finite.mem_toFinset] using hz
  have hxIcc := hd_Icc hxmem
  have hyIcc := hd_Icc hymem
  let m : ℝ := (x + y) / 2
  have hmIcc : m ∈ Icc a b := by
    constructor <;> dsimp only [m] <;> linarith [hxIcc.1, hxIcc.2, hyIcc.1, hyIcc.2]
  have hmcover := htcover hmIcc
  simp only [Set.mem_iUnion] at hmcover
  rcases hmcover with ⟨z, hz_t, hz_ball⟩
  have hznet : z ∈ net := by
    simpa only [net, Set.Finite.mem_toFinset] using hz_t
  have hzmem : z ∈ d := Finset.mem_union_right base hznet
  have hz_not_between : z ∉ Ioo x y :=
    no_mem_Ioo_orderedCut_succ d hi hzmem
  have hzside : z ≤ x ∨ y ≤ z := by
    by_contra h
    push Not at h
    exact hz_not_between h
  have hdist : |m - z| < ε / 4 := by
    simpa only [Metric.mem_ball, Real.dist_eq] using hz_ball
  rcases abs_lt.mp hdist with ⟨hdist_lower, hdist_upper⟩
  rcases hzside with hzx | hyz
  · dsimp only [x, y, m] at *
    linarith
  · dsimp only [x, y, m] at *
    linarith

/-- The hard compatibility gate in explicit form: prescribed cuts, two-sided endpoint escape, and
small adjacent mesh can be met by one finite division. -/
theorem exists_refinement_endpoints_divisionMesh_lt (S : Finset ℝ) (R : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ d : Finset ℝ,
      S ⊆ d ∧ leftEndpoint d ≤ -R ∧ R ≤ rightEndpoint d ∧ divisionMesh d < ε := by
  let T : Finset ℝ := insert (-R) (insert R S)
  obtain ⟨d, hTd, hdmesh⟩ := exists_refinement_divisionMesh_lt T hε
  have hneg : -R ∈ d := hTd (by simp only [T, Finset.mem_insert, true_or])
  have hpos : R ∈ d := hTd (by simp only [T, Finset.mem_insert, true_or, or_true])
  have hd : d.Nonempty := ⟨-R, hneg⟩
  refine ⟨d, ?_, ?_, ?_, hdmesh⟩
  · intro x hx
    exact hTd (by simp only [T, Finset.mem_insert]; exact Or.inr (Or.inr hx))
  · rw [leftEndpoint, orderedCut_zero_eq_min d hd]
    exact d.min'_le (-R) hneg
  · rw [rightEndpoint, orderedCut_bandCount_eq_max d hd]
    exact d.le_max' R hpos

/-- Candidate source filter: refinement of every fixed finite cut set together with global mesh
convergence to zero.  This is a tested candidate semantics, not a source-equivalence assertion. -/
noncomputable def stieltjesFilter : Filter (Finset ℝ) :=
  atTop ⊓ comap divisionMesh (nhds 0)

/-- The mesh and refinement requirements are simultaneously feasible. -/
theorem stieltjesFilter_neBot : NeBot stieltjesFilter := by
  rw [stieltjesFilter,
    (atTop_basis.inf_basis_neBot_iff (Metric.nhds_basis_ball.comap divisionMesh))]
  intro S _ ε hε
  obtain ⟨d, hSd, hdmesh⟩ := exists_refinement_divisionMesh_lt S hε
  refine ⟨d, hSd, ?_⟩
  simpa only [Set.mem_preimage, Metric.mem_ball, Real.dist_eq, sub_zero,
    abs_of_nonneg (divisionMesh_nonneg d)] using hdmesh

/-- The candidate filter is genuinely directed toward refinement of every finite prescribed set. -/
theorem tendsto_id_stieltjesFilter_atTop : Tendsto id stieltjesFilter atTop := by
  change stieltjesFilter ≤ atTop
  exact inf_le_left

/-- The global adjacent mesh tends to zero by construction of the candidate filter. -/
theorem tendsto_divisionMesh_stieltjesFilter :
    Tendsto divisionMesh stieltjesFilter (nhds 0) := by
  rw [tendsto_iff_comap]
  exact inf_le_right

/-- The minimum cut escapes to negative infinity; this is inherited from refinement cofinality. -/
theorem tendsto_leftEndpoint_stieltjesFilter :
    Tendsto (leftEndpoint : Finset ℝ → ℝ) stieltjesFilter atBot := by
  simpa only [Function.comp_id] using
    (tendsto_leftEndpoint_atBot.comp tendsto_id_stieltjesFilter_atTop)

/-- The maximum cut escapes to positive infinity; this is inherited from refinement cofinality. -/
theorem tendsto_rightEndpoint_stieltjesFilter :
    Tendsto (rightEndpoint : Finset ℝ → ℝ) stieltjesFilter atTop := by
  simpa only [Function.comp_id] using
    (tendsto_rightEndpoint_atTop.comp tendsto_id_stieltjesFilter_atTop)

/-- Adjoining a fixed finite cut set is eventually literally the identity. -/
theorem eventuallyEq_union_prescribed (c : Finset ℝ) :
    (fun d : Finset ℝ ↦ d ∪ c) =ᶠ[stieltjesFilter] id :=
  Scratch.DivisionRefinementCofinality.eventuallyEq_union_prescribed_of_tendsto_atTop
    c tendsto_id_stieltjesFilter_atTop

/-- Hence fixed prescribed-cut insertion preserves and reflects arbitrary target-filter limits. -/
theorem tendsto_union_prescribed_iff (c : Finset ℝ) {X : Type*}
    {f : Finset ℝ → X} {target : Filter X} :
    Tendsto (fun d ↦ f (d ∪ c)) stieltjesFilter target ↔
      Tendsto f stieltjesFilter target :=
  Scratch.DivisionRefinementCofinality.tendsto_union_prescribed_iff_of_tendsto_atTop
    c tendsto_id_stieltjesFilter_atTop

end Scratch.RadonStieltjesMeshFilter
