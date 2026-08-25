module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range

@[expose] public section

section IsSelfAdjoint

variable {A : Type*} [NonUnitalRing A] [StarRing A]
  [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
  [TopologicalSpace A] [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A]
  [IsTopologicalRing A] [ContinuousConstSMul ℝ A] [StarModule ℝ A] [ContinuousStar A] [T2Space A]

/-- A closed star subalgebra inherits the spectral order of its ambient algebra. -/
instance {S : Type*} [SetLike S A] [NonUnitalSubringClass S A] [SMulMemClass S ℝ A]
    [StarMemClass S A] (s : S) [IsClosed (s : Set A)] :
    StarOrderedRing s := by
  refine .of_nonneg_iff' add_le_add_right fun x ↦ ⟨fun hx ↦ ?_, ?_⟩
  · let r : A := CFC.sqrt (x : A)
    have hr : r ∈ s := by
      simp only [r, CFC.sqrt, cfcₙ_nnreal_eq_real _ (x : A) hx]
      exact cfcₙ_mem _ x.2
    refine ⟨⟨r, hr⟩, Subtype.ext ?_⟩
    simp [r, (CFC.sqrt_nonneg (x : A)).star_eq, CFC.sqrt_mul_sqrt_self (x : A)]
  · rintro ⟨x, rfl⟩
    exact star_mul_self_nonneg (x : A)

end IsSelfAdjoint

section IsStarNormal

variable {A : Type*} [NonUnitalRing A] [StarRing A]
  [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  [TopologicalSpace A] [NonUnitalContinuousFunctionalCalculus ℂ A IsStarNormal]
  [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A]
  [IsTopologicalRing A] [ContinuousConstSMul ℂ A] [StarModule ℂ A] [ContinuousStar A] [T2Space A]

/-- A closed complex star subalgebra inherits the spectral order of its ambient algebra. -/
instance {S : Type*} [SetLike S A] [NonUnitalSubringClass S A] [SMulMemClass S ℂ A]
    [StarMemClass S A] (s : S) [IsClosed (s : Set A)] :
    StarOrderedRing s := by
  have : SMulMemClass S ℝ A := ⟨fun r _ h ↦ SMulMemClass.smul_mem (r : ℂ) h⟩
  have : ContinuousConstSMul ℝ A :=
    Topology.IsInducing.id.continuousConstSMul Complex.ofReal (by simp)
  infer_instance

end IsStarNormal

variable {ι A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- If `x : ι → A` is summable and `y` is dominated by `x` (i.e., `0 ≤ y i ≤ x i` for `i : ι`), then
`y` is also summable. -/
lemma CStarAlgebra.dominated_convergence {x y : ι → A} (hx : Summable x)
    (hy_nonneg : ∀ i, 0 ≤ y i) (h_le : ∀ i, y i ≤ x i) : Summable y := by
  rw [summable_iff_vanishing] at hx ⊢
  intro u hu
  obtain ⟨ε, ε_pos, hε⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hu
  specialize hx (Metric.closedBall 0 ε) (Metric.closedBall_mem_nhds 0 ε_pos)
  peel hx with s t hst _
  refine hε ?_
  simp only [Metric.mem_closedBall, dist_zero_right] at this ⊢
  refine le_trans ?_ this
  refine CStarAlgebra.norm_le_norm_of_nonneg_of_le (t.sum_nonneg fun i _ ↦ (hy_nonneg i)) ?_
  gcongr
  exact h_le _

-- `Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric`
alias quasispectrum.norm_le_norm_of_mem :=
  NonUnitalIsometricContinuousFunctionalCalculus.norm_quasispectrum_le

open Unitization NNReal CStarAlgebra in
lemma CStarAlgebra.nnrpow_le_self_of_nonneg_of_norm_le_one {e : A} (he0 : 0 ≤ e) (he1 : ‖e‖ ≤ 1)
    {n : ℝ≥0} (hn : 1 ≤ n) : e ^ n ≤ e := by
  have : n ≠ 0 := by aesop
  conv_rhs => rw [← cfcₙ_id' ℝ e]
  rw [CFC.nnrpow_eq_cfcₙ_real e, ← sub_nonneg, ← cfcₙ_sub ..]
  refine cfcₙ_nonneg fun x hx ↦ sub_nonneg.mpr ?_
  have := quasispectrum.norm_le_norm_of_mem _ hx
  grw [he1, Real.norm_eq_abs] at this
  exact Real.rpow_le_self_of_le_one (quasispectrum_nonneg_of_nonneg _ he0 _ hx) (by grind) hn

/-- If `e` is an element of the nonnegative closed unit ball, then `e * e ≤ e`, with equality
if `e` is an extreme point
(see `isStarProjection_iff_mem_extremePoints_nonneg_and_mem_closedUnitBall`). -/
lemma CStarAlgebra.mul_self_le_of_nonneg_of_norm_le_one {e : A} (he0 : 0 ≤ e) (he1 : ‖e‖ ≤ 1) :
    e * e ≤ e := CFC.nnrpow_two e ▸ nnrpow_le_self_of_nonneg_of_norm_le_one he0 he1 one_le_two

open Unitization NNReal CStarAlgebra in
lemma CStarAlgebra.self_le_nnrpow_of_nonneg_of_norm_le_one {e : A} (he0 : 0 ≤ e) (he1 : ‖e‖ ≤ 1)
    {n : ℝ≥0} (hn0 : n ≠ 0) (hn : n ≤ 1) : e ≤ e ^ n := by
  conv_lhs => rw [← cfcₙ_id' ℝ e]
  rw [CFC.nnrpow_eq_cfcₙ_real e, ← sub_nonneg, ← cfcₙ_sub ..]
  refine cfcₙ_nonneg fun x hx ↦ sub_nonneg.mpr ?_
  have := quasispectrum.norm_le_norm_of_mem _ hx
  grw [he1, Real.norm_eq_abs] at this
  exact Real.self_le_rpow_of_le_one (quasispectrum_nonneg_of_nonneg _ he0 _ hx) (by grind) hn

lemma CStarAlgebra.self_le_sqrt_of_nonneg_of_norm_le_one {e : A} (he0 : 0 ≤ e) (he1 : ‖e‖ ≤ 1) :
    e ≤ CFC.sqrt e :=
  CFC.sqrt_eq_nnrpow e ▸ self_le_nnrpow_of_nonneg_of_norm_le_one he0 he1 (by simp) (by simp)
