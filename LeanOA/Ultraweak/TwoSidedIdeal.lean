module

public import LeanOA.Ultraweak.Opposite
public import LeanOA.Ultraweak.ProjectionLattice
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import Mathlib.RingTheory.TwoSidedIdeal.Lattice

@[expose] public section

/-!
# Ultraweakly closed two-sided ideals

This file identifies ultraweakly closed two-sided ideals in a W-star algebra with central
projections and transports the complete lattice structure across that correspondence.
-/

open Set
open scoped Ultraweak

namespace TwoSidedIdeal

variable {M P : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace P] in
/-- Ultraweak closedness of a two-sided ideal's underlying left ideal implies ultraweak closedness
of its underlying right ideal in the multiplicative opposite. -/
theorem isClosed_asIdealOpposite (J : TwoSidedIdeal M)
    (hJ : IsClosed (Ultraweak.ofSubmodule (P := P)
      (J.asIdeal.restrictScalars ℂ) : Set σ(M, P))) :
    IsClosed (Ultraweak.ofSubmodule (P := P)
      (J.asIdealOpposite.restrictScalars ℂ) : Set σ(Mᵐᵒᵖ, P)) := by
  let s : Set σ(M, P) := Ultraweak.ofSubmodule (P := P) (J.asIdeal.restrictScalars ℂ)
  rw [show (Ultraweak.ofSubmodule (P := P)
      (J.asIdealOpposite.restrictScalars ℂ) : Set σ(Mᵐᵒᵖ, P)) =
      Ultraweak.opCLE (𝕜 := ℂ) (M := M) (P := P) '' s by
    ext x
    constructor
    · intro hx
      refine ⟨(Ultraweak.opCLE (𝕜 := ℂ) (M := M) (P := P)).symm x, ?_, ?_⟩
      · have hx' := (Ultraweak.mem_ofSubmodule
            (J.asIdealOpposite.restrictScalars ℂ) x).mp hx
        change ofUltraweak x ∈ J.asIdealOpposite at hx'
        exact mem_asIdealOpposite.mp hx'
      · exact (Ultraweak.opCLE (𝕜 := ℂ) (M := M) (P := P)).apply_symm_apply x
    · rintro ⟨y, hy, rfl⟩
      change MulOpposite.op (ofUltraweak y) ∈ J.asIdealOpposite
      apply mem_asIdealOpposite.mpr
      have hy' := (Ultraweak.mem_ofSubmodule (J.asIdeal.restrictScalars ℂ) y).mp hy
      exact mem_asIdeal.mp hy']
  exact (Ultraweak.isClosed_image_opCLE_iff (M := M) (P := P) s).2 hJ

omit [PartialOrder M] [StarOrderedRing M] in
/-- An ultraweakly closed two-sided ideal of a W-star algebra is generated on both sides by a
unique central star projection. -/
theorem existsUnique_isStarProjection_mem_center_eq_span_of_isClosed_ultraweak
    (J : TwoSidedIdeal M)
    (hJ : IsClosed (Ultraweak.ofSubmodule (P := P)
      (J.asIdeal.restrictScalars ℂ) : Set σ(M, P))) :
    ∃! z : M, IsStarProjection z ∧ z ∈ Set.center M ∧
      J.asIdeal = Ideal.span {z} ∧
      J.asIdealOpposite = Ideal.span {MulOpposite.op z} := by
  obtain ⟨zₗ, ⟨hzₗ, hJzₗ⟩, hzₗ_unique⟩ :=
    Ideal.existsUnique_isStarProjection_eq_span_of_isClosed_ultraweak J.asIdeal hJ
  obtain ⟨zᵣ, ⟨hzᵣ, hJzᵣ⟩, -⟩ :=
    Ideal.existsUnique_isStarProjection_eq_span_op_of_isClosed_ultraweak J.asIdealOpposite
      (isClosed_asIdealOpposite J hJ)
  have hzₗJ : zₗ ∈ J := by
    rw [← mem_asIdeal, hJzₗ]
    exact Ideal.subset_span (Set.mem_singleton zₗ)
  have hzᵣJ : zᵣ ∈ J := by
    apply mem_asIdealOpposite.mp
    rw [hJzᵣ]
    exact Ideal.subset_span (Set.mem_singleton (MulOpposite.op zᵣ))
  have hmul_zₗ {x : M} (hx : x ∈ J) : x * zₗ = x := by
    have hx' : x ∈ Ideal.span {zₗ} := by
      rw [← hJzₗ, mem_asIdeal]
      exact hx
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hx'
    rw [← ha, mul_assoc, hzₗ.isIdempotentElem.eq]
  have hzᵣ_mul {x : M} (hx : x ∈ J) : zᵣ * x = x := by
    have hx' : MulOpposite.op x ∈ Ideal.span {MulOpposite.op zᵣ} := by
      rw [← hJzᵣ, mem_asIdealOpposite]
      exact hx
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hx'
    have ha' := congr_arg MulOpposite.unop ha
    have ha'' : zᵣ * a.unop = x := by
      simpa only [MulOpposite.unop_mul, MulOpposite.unop_op] using ha'
    calc
      zᵣ * x = zᵣ * (zᵣ * a.unop) := by rw [ha'']
      _ = (zᵣ * zᵣ) * a.unop := (mul_assoc _ _ _).symm
      _ = zᵣ * a.unop := by rw [hzᵣ.isIdempotentElem.eq]
      _ = x := ha''
  have hz : zₗ = zᵣ := by
    calc
      zₗ = zᵣ * zₗ := (hzᵣ_mul hzₗJ).symm
      _ = zᵣ := hmul_zₗ hzᵣJ
  subst zᵣ
  have hz_center : zₗ ∈ Set.center M := by
    rw [Semigroup.mem_center_iff]
    intro x
    calc
      x * zₗ = zₗ * (x * zₗ) := (hzᵣ_mul (J.mul_mem_left x zₗ hzₗJ)).symm
      _ = (zₗ * x) * zₗ := by rw [mul_assoc]
      _ = zₗ * x := hmul_zₗ (J.mul_mem_right zₗ x hzₗJ)
  refine ⟨zₗ, ⟨hzₗ, hz_center, hJzₗ, hJzᵣ⟩, ?_⟩
  intro z hz
  exact hzₗ_unique z ⟨hz.1, hz.2.2.1⟩

/-- Ultraweakly closed two-sided ideals, represented with Mathlib's native `TwoSidedIdeal`. -/
abbrev UltraweakClosed (M P : Type*) [CStarAlgebra M]
    [NormedAddCommGroup P] [NormedSpace ℂ P] [Predual ℂ M P] :=
  {J : TwoSidedIdeal M // IsClosed (Ultraweak.ofSubmodule (P := P)
    (J.asIdeal.restrictScalars ℂ) : Set σ(M, P))}

/-- The complete lattice structure on ultraweakly closed two-sided ideals for a specified
predual. -/
@[implicit_reducible]
noncomputable def completeLatticeUltraweakClosed : CompleteLattice (UltraweakClosed M P) := by
  let infimum : Set (UltraweakClosed M P) → UltraweakClosed M P := fun s ↦
    ⟨⨅ J : s, J.1.1, by
      rw [show ((⨅ J : s, J.1.1).asIdeal.restrictScalars ℂ) =
          ⨅ J : s, J.1.1.asIdeal.restrictScalars ℂ by
        ext x
        simp only [Submodule.restrictScalars_mem, mem_asIdeal, mem_iInf, Submodule.mem_iInf,
          Subtype.forall]]
      exact Ultraweak.isClosed_iInf_ofSubmodule _ fun J ↦ J.1.2⟩
  letI : InfSet (UltraweakClosed M P) := ⟨infimum⟩
  refine completeLatticeOfInf _ ?_
  intro s
  constructor
  · intro J hJ
    change (⨅ K : s, K.1.1) ≤ J.1
    exact iInf_le_of_le (⟨J, hJ⟩ : s) le_rfl
  · intro J hJ
    change J.1 ≤ ⨅ K : s, K.1.1
    exact le_iInf fun K ↦ hJ K.2

end TwoSidedIdeal

namespace IsStarProjection

/-- Central star projections, represented as a subtype of Mathlib's star-projection subtype. -/
abbrev Central (M : Type*) [Semigroup M] [Star M] :=
  {p : {p : M // IsStarProjection p} // p.1 ∈ Set.center M}

namespace Central

variable {M P : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]

/-- The two-sided ideal generated by a central projection. -/
def span (z : Central M) : TwoSidedIdeal M := by
  letI : (Ideal.span {z.1.1}).IsTwoSided := ⟨fun b hx ↦ by
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hx
    apply Ideal.mem_span_singleton'.mpr
    refine ⟨a * b, ?_⟩
    calc
      (a * b) * z.1.1 = a * (b * z.1.1) := mul_assoc _ _ _
      _ = a * (z.1.1 * b) := by rw [Semigroup.mem_center_iff.mp z.2 b]
      _ = (a * z.1.1) * b := (mul_assoc _ _ _).symm
      _ = _ := congr_arg (· * b) ha⟩
  exact (Ideal.span {z.1.1}).toTwoSided

omit [PartialOrder M] [StarOrderedRing M] in
@[simp]
theorem span_asIdeal (z : Central M) : (span z).asIdeal = Ideal.span {z.1.1} := by
  simp [span]

omit [PartialOrder M] [StarOrderedRing M] in
@[simp]
theorem span_asIdealOpposite (z : Central M) :
    (span z).asIdealOpposite = Ideal.span {MulOpposite.op z.1.1} := by
  ext x
  rw [TwoSidedIdeal.mem_asIdealOpposite, Ideal.mem_span_singleton']
  constructor
  · intro hx
    have hx' : x.unop ∈ Ideal.span {z.1.1} := by
      rw [← span_asIdeal z, TwoSidedIdeal.mem_asIdeal]
      exact hx
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hx'
    refine ⟨MulOpposite.op a, ?_⟩
    apply MulOpposite.unop_injective
    simpa only [MulOpposite.unop_mul, MulOpposite.unop_op] using
      (Semigroup.mem_center_iff.mp z.2 a).symm.trans ha
  · rintro ⟨a, ha⟩
    apply TwoSidedIdeal.mem_asIdeal.mp
    rw [span_asIdeal]
    apply Ideal.mem_span_singleton'.mpr
    refine ⟨a.unop, ?_⟩
    have ha' := congr_arg MulOpposite.unop ha
    simpa only [MulOpposite.unop_mul, MulOpposite.unop_op] using
      (Semigroup.mem_center_iff.mp z.2 a.unop).trans ha'

theorem span_le_span_iff (z w : Central M) : span z ≤ span w ↔ z ≤ w := by
  rw [show span z ≤ span w ↔ (span z).asIdeal ≤ (span w).asIdeal by
    simp only [SetLike.le_def, TwoSidedIdeal.mem_asIdeal],
    span_asIdeal, span_asIdeal, z.1.2.span_singleton_le_span_singleton_iff w.1.2]
  rfl

/-- The central projection generating an ultraweakly closed two-sided ideal. -/
noncomputable def centralGenerator (J : TwoSidedIdeal.UltraweakClosed M P) : Central M :=
  let h := TwoSidedIdeal.existsUnique_isStarProjection_mem_center_eq_span_of_isClosed_ultraweak
    J.1 J.2
  ⟨⟨h.choose, h.choose_spec.1.1⟩, h.choose_spec.1.2.1⟩

omit [PartialOrder M] [StarOrderedRing M] in
theorem centralGenerator_asIdeal (J : TwoSidedIdeal.UltraweakClosed M P) :
    J.1.asIdeal = Ideal.span {(centralGenerator J : M)} := by
  simp only [centralGenerator]
  exact (TwoSidedIdeal.existsUnique_isStarProjection_mem_center_eq_span_of_isClosed_ultraweak
    J.1 J.2).choose_spec.1.2.2.1

omit [PartialOrder M] [StarOrderedRing M] in
theorem centralGenerator_asIdealOpposite (J : TwoSidedIdeal.UltraweakClosed M P) :
    J.1.asIdealOpposite = Ideal.span {MulOpposite.op (centralGenerator J : M)} := by
  simp only [centralGenerator]
  exact (TwoSidedIdeal.existsUnique_isStarProjection_mem_center_eq_span_of_isClosed_ultraweak
    J.1 J.2).choose_spec.1.2.2.2

/-- A projection lies in a closed two-sided ideal exactly when it is below the ideal's central
generator. -/
theorem le_centralGenerator_iff_mem (p : {p : M // IsStarProjection p})
    (J : TwoSidedIdeal.UltraweakClosed M P) :
    p ≤ (centralGenerator J).1 ↔ p.1 ∈ J.1 := by
  change p.1 ≤ (centralGenerator J).1.1 ↔ p.1 ∈ J.1
  rw [← p.2.span_singleton_le_span_singleton_iff (centralGenerator J).1.2,
    ← centralGenerator_asIdeal J]
  constructor
  · intro h
    exact TwoSidedIdeal.mem_asIdeal.mp (h (Ideal.subset_span (Set.mem_singleton p.1)))
  · intro hp
    apply Ideal.span_le.mpr
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    change p.1 ∈ J.1
    exact hp

theorem centralGenerator_mem (J : TwoSidedIdeal.UltraweakClosed M P) :
    (centralGenerator J).1.1 ∈ J.1 :=
  (le_centralGenerator_iff_mem (centralGenerator J).1 J).mp le_rfl

@[simp]
theorem centralGenerator_span (z : Central M) :
    centralGenerator (⟨span z, by
      rw [span_asIdeal]
      exact z.1.2.isClosed_span_singleton_ultraweak (P := P)⟩ :
        TwoSidedIdeal.UltraweakClosed M P) = z := by
  let hclosed : IsClosed (Ultraweak.ofSubmodule (P := P)
      ((span z).asIdeal.restrictScalars ℂ) : Set σ(M, P)) := by
    rw [span_asIdeal]
    exact z.1.2.isClosed_span_singleton_ultraweak (P := P)
  let h := TwoSidedIdeal.existsUnique_isStarProjection_mem_center_eq_span_of_isClosed_ultraweak
    (span z) hclosed
  apply Subtype.ext
  apply Subtype.ext
  exact h.unique h.choose_spec.1
    ⟨z.1.2, z.2, span_asIdeal z, span_asIdealOpposite z⟩

/-- Central projections are order-isomorphic to ultraweakly closed two-sided ideals. -/
noncomputable def orderIsoUltraweakClosedTwoSidedIdeal :
    Central M ≃o TwoSidedIdeal.UltraweakClosed M P where
  toFun z := ⟨span z, by
    rw [span_asIdeal]
    exact z.1.2.isClosed_span_singleton_ultraweak (P := P)⟩
  invFun := centralGenerator
  left_inv := centralGenerator_span
  right_inv J := by
    apply Subtype.ext
    apply TwoSidedIdeal.ext
    intro x
    constructor
    · intro hx
      apply TwoSidedIdeal.mem_asIdeal.mp
      rw [centralGenerator_asIdeal, ← span_asIdeal]
      exact TwoSidedIdeal.mem_asIdeal.mpr hx
    · intro hx
      apply TwoSidedIdeal.mem_asIdeal.mp
      rw [span_asIdeal, ← centralGenerator_asIdeal]
      exact TwoSidedIdeal.mem_asIdeal.mpr hx
  map_rel_iff' := span_le_span_iff _ _

/-- The canonical complete lattice of central projections in a W-star algebra.

It is built with `completeLatticeOfInf` so that its order is definitionally the ambient subtype
order, avoiding an instance diamond between the transported order and the existing subtype order.
-/
noncomputable instance instCompleteLatticeCentralOfWStarAlgebra
    {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] [WStarAlgebra M] :
    CompleteLattice (Central M) := by
  let P := WStarAlgebra.predual M
  letI : CompleteLattice (TwoSidedIdeal.UltraweakClosed M P) :=
    TwoSidedIdeal.completeLatticeUltraweakClosed
  let e := orderIsoUltraweakClosedTwoSidedIdeal (M := M) (P := P)
  let infimum : Set (Central M) → Central M := fun s ↦ e.symm (⨅ z : s, e z.1)
  letI : InfSet (Central M) := ⟨infimum⟩
  refine completeLatticeOfInf _ ?_
  intro s
  constructor
  · intro z hz
    change e.symm (⨅ w : s, e w.1) ≤ z
    rw [← e.le_iff_le, e.apply_symm_apply]
    exact iInf_le_of_le (⟨z, hz⟩ : s) le_rfl
  · intro z hz
    change z ≤ e.symm (⨅ w : s, e w.1)
    rw [← e.le_iff_le, e.apply_symm_apply]
    exact le_iInf fun w : s ↦ e.monotone (hz w.2)

end Central

end IsStarProjection
