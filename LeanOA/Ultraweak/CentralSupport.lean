module

public import LeanOA.Ultraweak.Annihilator
public import LeanOA.Ultraweak.TwoSidedIdeal

@[expose] public section

/-!
# Central support

This file defines the central support of a projection in a W-star algebra and proves its
closure-operator laws and Sakai's orthogonality theorem.
-/

open Set
open scoped Ultraweak

namespace IsStarProjection.Central

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

/-- The complement of a central projection, bundled as a central projection. -/
def oneSub (z : Central M) : Central M :=
  ⟨⟨1 - z.1.1, z.1.2.one_sub⟩, by
    rw [Semigroup.mem_center_iff]
    intro x
    rw [mul_sub, sub_mul, mul_one, one_mul, Semigroup.mem_center_iff.mp z.2 x]⟩

omit [PartialOrder M] [StarOrderedRing M] in
@[simp]
theorem oneSub_val (z : Central M) : (oneSub z).1.1 = 1 - z.1.1 :=
  rfl

omit [PartialOrder M] [StarOrderedRing M] in
@[simp]
theorem oneSub_oneSub (z : Central M) : oneSub (oneSub z) = z := by
  apply Subtype.ext
  apply Subtype.ext
  exact sub_sub_cancel 1 z.1.1

end IsStarProjection.Central

namespace WStarAlgebra

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] [WStarAlgebra M]

open IsStarProjection

/-- The central support of a projection is the infimum of the central projections above it. -/
noncomputable def centralSupport (p : {p : M // IsStarProjection p}) : Central M :=
  sInf {z | p ≤ z.1}

private theorem exists_isLeast_central_ge (p : {p : M // IsStarProjection p}) :
    ∃ c : Central M, IsLeast {z : Central M | p ≤ z.1} c := by
  let I : Ideal Mᵐᵒᵖ := Ideal.span {MulOpposite.op p.1}
  let J : TwoSidedIdeal M := TwoSidedIdeal.annihilatorOfIdealOpposite I
  have hJ : IsClosed (Ultraweak.ofSubmodule (P := WStarAlgebra.predual M)
      (J.asIdeal.restrictScalars ℂ) : Set σ(M, WStarAlgebra.predual M)) := by
    exact TwoSidedIdeal.isClosed_annihilatorOfIdealOpposite (P := WStarAlgebra.predual M) I
  let Jc : TwoSidedIdeal.UltraweakClosed M (WStarAlgebra.predual M) := ⟨J, hJ⟩
  let z : Central M := Central.centralGenerator Jc
  let c : Central M := Central.oneSub z
  refine ⟨c, ?_⟩
  constructor
  · change p.1 ≤ 1 - z.1.1
    apply (p.2.mul_eq_zero_iff_le_one_sub z.1.2).mp
    have hzJ : z.1.1 ∈ J := Central.centralGenerator_mem Jc
    exact (TwoSidedIdeal.mem_annihilatorOfIdealOpposite.mp hzJ)
      (MulOpposite.op p.1) (Ideal.subset_span (Set.mem_singleton (MulOpposite.op p.1)))
  · intro w hpw
    change 1 - z.1.1 ≤ w.1.1
    have hpw_mul : p.1 * w.1.1 = p.1 :=
      (p.2.le_iff_mul_eq_left w.1.2).mp hpw
    have hcompJ : 1 - w.1.1 ∈ J := by
      apply TwoSidedIdeal.mem_annihilatorOfIdealOpposite.mpr
      intro y hy
      obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hy
      have hy' : p.1 * a.unop = y.unop := by
        simpa only [MulOpposite.unop_mul, MulOpposite.unop_op] using
          congr_arg MulOpposite.unop ha
      rw [← hy']
      calc
        (p.1 * a.unop) * (1 - w.1.1) =
            p.1 * a.unop - (p.1 * a.unop) * w.1.1 := by rw [mul_sub, mul_one]
        _ = p.1 * a.unop - p.1 * (a.unop * w.1.1) := by rw [mul_assoc]
        _ = p.1 * a.unop - p.1 * (w.1.1 * a.unop) := by
          rw [Semigroup.mem_center_iff.mp w.2 a.unop]
        _ = p.1 * a.unop - (p.1 * w.1.1) * a.unop := by rw [mul_assoc]
        _ = 0 := by rw [hpw_mul, sub_self]
    have hcomp_span : 1 - w.1.1 ∈ Ideal.span {z.1.1} := by
      rw [← Central.centralGenerator_asIdeal Jc, TwoSidedIdeal.mem_asIdeal]
      exact hcompJ
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hcomp_span
    have hmul : (1 - w.1.1) * z.1.1 = 1 - w.1.1 := by
      rw [← ha, mul_assoc, z.1.2.isIdempotentElem.eq]
    have hcomp_le : 1 - w.1.1 ≤ z.1.1 :=
      (w.1.2.one_sub.le_iff_mul_eq_left z.1.2).mpr hmul
    rw [sub_le_iff_le_add] at hcomp_le ⊢
    simpa only [add_comm] using hcomp_le

private theorem centralSupport_spec (p : {p : M // IsStarProjection p}) :
    IsLeast {z : Central M | p ≤ z.1} (centralSupport p) := by
  obtain ⟨c, hc⟩ := exists_isLeast_central_ge p
  have h : centralSupport p = c :=
    (isGLB_sInf {z : Central M | p ≤ z.1}).unique hc.isGLB
  rw [h]
  exact hc

/-- A projection is below its central support. -/
theorem le_centralSupport (p : {p : M // IsStarProjection p}) :
    p ≤ (centralSupport p).1 :=
  (centralSupport_spec p).1

/-- The central support is the least central projection above a projection. -/
theorem centralSupport_le_iff (p : {p : M // IsStarProjection p}) (z : Central M) :
    centralSupport p ≤ z ↔ p ≤ z.1 := by
  constructor
  · exact fun h ↦ (le_centralSupport p).trans h
  · intro h
    exact (centralSupport_spec p).2 h

/-- Central support is monotone. -/
theorem centralSupport_mono {p q : {p : M // IsStarProjection p}} (h : p ≤ q) :
    centralSupport p ≤ centralSupport q :=
  (centralSupport_le_iff p (centralSupport q)).2 (h.trans (le_centralSupport q))

/-- The central support of a central projection is itself. -/
@[simp]
theorem centralSupport_central (z : Central M) : centralSupport z.1 = z := by
  apply le_antisymm
  · exact (centralSupport_le_iff z.1 z).2 le_rfl
  · exact le_centralSupport z.1

/-- Taking central support twice has no further effect. -/
theorem centralSupport_idem (p : {p : M // IsStarProjection p}) :
    centralSupport (centralSupport p).1 = centralSupport p :=
  centralSupport_central (centralSupport p)

/-- A projection equals its central support exactly when it is central. -/
theorem centralSupport_eq_iff_mem_center (p : {p : M // IsStarProjection p}) :
    (centralSupport p).1 = p ↔ p.1 ∈ Set.center M := by
  constructor
  · intro h
    rw [← h]
    exact (centralSupport p).2
  · intro hp
    exact congr_arg Subtype.val (centralSupport_central (⟨p, hp⟩ : Central M))

/-- Sakai 1.10.7: if `p * x * q = 0` for every `x`, then the central supports of `p`
and `q` are orthogonal. -/
theorem centralSupport_mul_centralSupport_eq_zero_of_forall_mul_mul_eq_zero
    (p q : {p : M // IsStarProjection p}) (h : ∀ x : M, p.1 * x * q.1 = 0) :
    (centralSupport p).1.1 * (centralSupport q).1.1 = 0 := by
  let I : Ideal Mᵐᵒᵖ := Ideal.span {MulOpposite.op p.1}
  let J : TwoSidedIdeal M := TwoSidedIdeal.annihilatorOfIdealOpposite I
  have hJ : IsClosed (Ultraweak.ofSubmodule (P := WStarAlgebra.predual M)
      (J.asIdeal.restrictScalars ℂ) : Set σ(M, WStarAlgebra.predual M)) :=
    TwoSidedIdeal.isClosed_annihilatorOfIdealOpposite (P := WStarAlgebra.predual M) I
  let Jc : TwoSidedIdeal.UltraweakClosed M (WStarAlgebra.predual M) := ⟨J, hJ⟩
  let z : Central M := Central.centralGenerator Jc
  have hqJ : q.1 ∈ J := by
    apply TwoSidedIdeal.mem_annihilatorOfIdealOpposite.mpr
    intro y hy
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hy
    have hy' : p.1 * a.unop = y.unop := by
      simpa only [MulOpposite.unop_mul, MulOpposite.unop_op] using
        congr_arg MulOpposite.unop ha
    rw [← hy']
    exact h a.unop
  have hqz : q ≤ z.1 := (Central.le_centralGenerator_iff_mem q Jc).mpr hqJ
  have hcz : centralSupport q ≤ z := (centralSupport_le_iff q z).mpr hqz
  have hzJ : z.1.1 ∈ J := Central.centralGenerator_mem Jc
  have hpz : p.1 * z.1.1 = 0 :=
    (TwoSidedIdeal.mem_annihilatorOfIdealOpposite.mp hzJ)
      (MulOpposite.op p.1) (Ideal.subset_span (Set.mem_singleton (MulOpposite.op p.1)))
  have hcqz : (centralSupport q).1.1 * z.1.1 = (centralSupport q).1.1 :=
    ((centralSupport q).1.2.le_iff_mul_eq_left z.1.2).mp hcz
  have hpcq : p.1 * (centralSupport q).1.1 = 0 := by
    calc
      p.1 * (centralSupport q).1.1 =
          p.1 * ((centralSupport q).1.1 * z.1.1) := by rw [hcqz]
      _ = p.1 * (z.1.1 * (centralSupport q).1.1) := by
        rw [Semigroup.mem_center_iff.mp z.2 (centralSupport q).1.1]
      _ = (p.1 * z.1.1) * (centralSupport q).1.1 := (mul_assoc _ _ _).symm
      _ = 0 := by rw [hpz, zero_mul]
  have hpcomp : p ≤ (Central.oneSub (centralSupport q)).1 := by
    exact (p.2.mul_eq_zero_iff_le_one_sub (centralSupport q).1.2).mp hpcq
  have hcpcomp : centralSupport p ≤ Central.oneSub (centralSupport q) :=
    (centralSupport_le_iff p (Central.oneSub (centralSupport q))).mpr hpcomp
  exact ((centralSupport p).1.2.mul_eq_zero_iff_le_one_sub
    (centralSupport q).1.2).mpr hcpcomp

/-- The reusable iff form of Sakai 1.10.7. -/
theorem centralSupport_mul_centralSupport_eq_zero_iff
    (p q : {p : M // IsStarProjection p}) :
    (centralSupport p).1.1 * (centralSupport q).1.1 = 0 ↔
      ∀ x : M, p.1 * x * q.1 = 0 := by
  constructor
  · intro hcentral x
    have hp : p.1 * (centralSupport p).1.1 = p.1 :=
      (p.2.le_iff_mul_eq_left (centralSupport p).1.2).mp (le_centralSupport p)
    have hq : (centralSupport q).1.1 * q.1 = q.1 :=
      (q.2.le_iff_mul_eq_right (centralSupport q).1.2).mp (le_centralSupport q)
    calc
      p.1 * x * q.1 = (p.1 * (centralSupport p).1.1) * x * q.1 := by rw [hp]
      _ = p.1 * ((centralSupport p).1.1 * x) * q.1 := by simp only [mul_assoc]
      _ = p.1 * (x * (centralSupport p).1.1) * q.1 := by
        rw [← Semigroup.mem_center_iff.mp (centralSupport p).2 x]
      _ = (p.1 * x) * (centralSupport p).1.1 * q.1 := by simp only [mul_assoc]
      _ = (p.1 * x) * (centralSupport p).1.1 *
          ((centralSupport q).1.1 * q.1) := by rw [hq]
      _ = (p.1 * x) *
          ((centralSupport p).1.1 * (centralSupport q).1.1) * q.1 := by
        simp only [mul_assoc]
      _ = 0 := by rw [hcentral, mul_zero, zero_mul]
  · exact centralSupport_mul_centralSupport_eq_zero_of_forall_mul_mul_eq_zero p q

end WStarAlgebra
