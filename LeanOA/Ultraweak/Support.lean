module

public import LeanOA.Ultraweak.Annihilator
public import LeanOA.Ultraweak.NonUnitalStarSubalgebra
public import LeanOA.Ultraweak.ProjectionLattice

@[expose] public section

/-!
# Support projections

This file defines the left and right support projections of an element of a W-star algebra using
the canonical complete lattice of star projections. The definitions do not retain a choice of
predual.
-/

namespace WStarAlgebra

open scoped Ultraweak

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] [WStarAlgebra M]

/-- The left support of an element is the infimum of the projections which act as a left identity
on it. -/
noncomputable def leftSupport (a : M) : {p : M // IsStarProjection p} :=
  sInf {p | p.1 * a = a}

/-- The right support of an element is the infimum of the projections which act as a right identity
on it. -/
noncomputable def rightSupport (a : M) : {p : M // IsStarProjection p} :=
  sInf {p | a * p.1 = a}

private theorem leftSupport_spec (a : M) :
    (leftSupport a).1 * a = a ∧
      Ideal.leftAnnihilator {a} = Ideal.span {1 - (leftSupport a).1} := by
  let P := WStarAlgebra.predual M
  let I := Ideal.leftAnnihilator {a}
  have hI : IsClosed (Ultraweak.ofSubmodule (P := P)
      (I.restrictScalars ℂ) : Set σ(M, P)) :=
    Ideal.isClosed_leftAnnihilator (P := P) {a}
  obtain ⟨e, ⟨he, hIe⟩, -⟩ :=
    Ideal.existsUnique_isStarProjection_eq_span_of_isClosed_ultraweak I hI
  let p : {p : M // IsStarProjection p} := ⟨1 - e, he.one_sub⟩
  have hea : e * a = 0 := by
    apply (Ideal.mem_leftAnnihilator (s := {a}) (x := e)).mp
      (show e ∈ I by rw [hIe]; exact Ideal.subset_span (Set.mem_singleton e))
      a (Set.mem_singleton a)
  have hp : IsLeast {q : {p : M // IsStarProjection p} | q.1 * a = a} p := by
    constructor
    · change (1 - e) * a = a
      rw [sub_mul, one_mul, hea, sub_zero]
    · intro q hq
      have hcomp : 1 - q.1 ∈ I := by
        rw [Ideal.mem_leftAnnihilator]
        intro x hx
        rw [Set.mem_singleton_iff.mp hx, sub_mul, one_mul, hq, sub_self]
      rw [hIe] at hcomp
      obtain ⟨x, hx⟩ := Ideal.mem_span_singleton'.mp hcomp
      have hmul : (1 - q.1) * e = 1 - q.1 := by
        rw [← hx, mul_assoc, he.isIdempotentElem.eq]
      have hle : 1 - q.1 ≤ e :=
        (q.2.one_sub.le_iff_mul_eq_left he).2 hmul
      change 1 - e ≤ q.1
      rw [sub_le_iff_le_add] at hle ⊢
      simpa only [add_comm] using hle
  have hpe : leftSupport a = p :=
    (isGLB_sInf {q : {p : M // IsStarProjection p} | q.1 * a = a}).unique hp.isGLB
  refine ⟨hpe ▸ hp.1, ?_⟩
  rw [hpe]
  change I = Ideal.span {1 - (1 - e)}
  simpa only [sub_sub_cancel] using hIe

private theorem rightSupport_spec (a : M) :
    a * (rightSupport a).1 = a ∧
      Ideal.rightAnnihilator {a} =
        Ideal.span {MulOpposite.op (1 - (rightSupport a).1)} := by
  let P := WStarAlgebra.predual M
  let I := Ideal.rightAnnihilator {a}
  have hI : IsClosed (Ultraweak.ofSubmodule (P := P)
      (I.restrictScalars ℂ) : Set σ(Mᵐᵒᵖ, P)) :=
    Ideal.isClosed_rightAnnihilator (P := P) {a}
  obtain ⟨e, ⟨he, hIe⟩, -⟩ :=
    Ideal.existsUnique_isStarProjection_eq_span_op_of_isClosed_ultraweak I hI
  let p : {p : M // IsStarProjection p} := ⟨1 - e, he.one_sub⟩
  have hae : a * e = 0 := by
    apply (Ideal.mem_rightAnnihilator (s := {a}) (x := MulOpposite.op e)).mp
      (show MulOpposite.op e ∈ I by
        rw [hIe]
        exact Ideal.subset_span (Set.mem_singleton (MulOpposite.op e)))
      a (Set.mem_singleton a)
  have hp : IsLeast {q : {p : M // IsStarProjection p} | a * q.1 = a} p := by
    constructor
    · change a * (1 - e) = a
      rw [mul_sub, mul_one, hae, sub_zero]
    · intro q hq
      have hcomp : MulOpposite.op (1 - q.1) ∈ I := by
        rw [Ideal.mem_rightAnnihilator]
        intro x hx
        rw [Set.mem_singleton_iff.mp hx, MulOpposite.unop_op, mul_sub, mul_one, hq,
          sub_self]
      rw [hIe] at hcomp
      obtain ⟨x, hx⟩ := Ideal.mem_span_singleton'.mp hcomp
      have hx' : e * x.unop = 1 - q.1 := by
        simpa only [MulOpposite.unop_mul, MulOpposite.unop_op] using
          congr_arg MulOpposite.unop hx
      have hmul : e * (1 - q.1) = 1 - q.1 := by
        rw [← hx', ← mul_assoc, he.isIdempotentElem.eq, hx']
      have hle : 1 - q.1 ≤ e :=
        (q.2.one_sub.le_iff_mul_eq_right he).2 hmul
      change 1 - e ≤ q.1
      rw [sub_le_iff_le_add] at hle ⊢
      simpa only [add_comm] using hle
  have hpe : rightSupport a = p :=
    (isGLB_sInf {q : {p : M // IsStarProjection p} | a * q.1 = a}).unique hp.isGLB
  refine ⟨hpe ▸ hp.1, ?_⟩
  rw [hpe]
  change I = Ideal.span {MulOpposite.op (1 - (1 - e))}
  simpa only [sub_sub_cancel] using hIe

/-- The left support acts as a left identity on its element. -/
@[simp]
theorem leftSupport_mul (a : M) : (leftSupport a).1 * a = a :=
  (leftSupport_spec a).1

/-- The right support acts as a right identity on its element. -/
@[simp]
theorem mul_rightSupport (a : M) : a * (rightSupport a).1 = a :=
  (rightSupport_spec a).1

/-- The left support is the least projection which acts as a left identity. -/
theorem leftSupport_le_iff (a : M) (p : {p : M // IsStarProjection p}) :
    leftSupport a ≤ p ↔ p.1 * a = a := by
  constructor
  · intro h
    rw [← leftSupport_mul a, ← mul_assoc,
      (leftSupport a).2.le_iff_mul_eq_right p.2 |>.mp h]
  · intro hp
    exact sInf_le (s := {q : {p : M // IsStarProjection p} | q.1 * a = a}) hp

/-- The right support is the least projection which acts as a right identity. -/
theorem rightSupport_le_iff (a : M) (p : {p : M // IsStarProjection p}) :
    rightSupport a ≤ p ↔ a * p.1 = a := by
  constructor
  · intro h
    rw [← mul_rightSupport a, mul_assoc,
      (rightSupport a).2.le_iff_mul_eq_left p.2 |>.mp h]
  · intro hp
    exact sInf_le (s := {q : {p : M // IsStarProjection p} | a * q.1 = a}) hp

/-- The left annihilator of one element is generated by the complement of its left support. -/
theorem leftAnnihilator_singleton_eq_span (a : M) :
    Ideal.leftAnnihilator {a} = Ideal.span {1 - (leftSupport a).1} :=
  (leftSupport_spec a).2

/-- The right annihilator of one element is generated by the complement of its right support. -/
theorem rightAnnihilator_singleton_eq_span (a : M) :
    Ideal.rightAnnihilator {a} =
      Ideal.span {MulOpposite.op (1 - (rightSupport a).1)} :=
  (rightSupport_spec a).2

/-- Multiplication on the right by the left support has the same kernel as multiplication on the
right by the original element. -/
theorem mul_leftSupport_eq_zero_iff (a b : M) :
    b * (leftSupport a).1 = 0 ↔ b * a = 0 := by
  constructor
  · intro h
    rw [← leftSupport_mul a, ← mul_assoc, h, zero_mul]
  · intro h
    have hb : b ∈ Ideal.leftAnnihilator {a} := by
      rw [Ideal.mem_leftAnnihilator]
      intro x hx
      simpa only [Set.mem_singleton_iff.mp hx] using h
    rw [leftAnnihilator_singleton_eq_span] at hb
    obtain ⟨x, hx⟩ := Ideal.mem_span_singleton'.mp hb
    rw [← hx, mul_assoc, sub_mul, one_mul, (leftSupport a).2.isIdempotentElem.eq,
      sub_self, mul_zero]

/-- Taking adjoints exchanges left and right support. -/
@[simp]
theorem leftSupport_star (a : M) : leftSupport (star a) = rightSupport a := by
  apply le_antisymm
  · rw [leftSupport_le_iff]
    simpa only [star_mul, star_star, (rightSupport a).2.isSelfAdjoint.star_eq] using
      congr_arg star (mul_rightSupport a)
  · rw [rightSupport_le_iff]
    simpa only [star_mul, star_star, (leftSupport (star a)).2.isSelfAdjoint.star_eq] using
      congr_arg star (leftSupport_mul (star a))

/-- Taking adjoints exchanges right and left support. -/
@[simp]
theorem rightSupport_star (a : M) : rightSupport (star a) = leftSupport a := by
  rw [← leftSupport_star, star_star]

/-- Multiplication on the left by the right support has the same kernel as multiplication on the
left by the original element. -/
theorem rightSupport_mul_eq_zero_iff (a b : M) :
    (rightSupport a).1 * b = 0 ↔ a * b = 0 := by
  constructor
  · intro h
    have hs : star b * (leftSupport (star a)).1 = 0 := by
      rw [leftSupport_star]
      simpa only [star_mul, (rightSupport a).2.isSelfAdjoint.star_eq, star_zero] using
        congr_arg star h
    have hsa := (mul_leftSupport_eq_zero_iff (star a) (star b)).mp hs
    simpa only [star_mul, star_star, star_zero] using congr_arg star hsa
  · intro h
    have hsa : star b * star a = 0 := by
      simpa only [star_mul, star_zero] using congr_arg star h
    have hs := (mul_leftSupport_eq_zero_iff (star a) (star b)).mpr hsa
    rw [leftSupport_star] at hs
    simpa only [star_mul, star_star, (rightSupport a).2.isSelfAdjoint.star_eq, star_zero] using
      congr_arg star hs

/-- Left and right support agree on a self-adjoint element. -/
theorem IsSelfAdjoint.leftSupport_eq_rightSupport {a : M} (ha : IsSelfAdjoint a) :
    leftSupport a = rightSupport a := by
  rw [← leftSupport_star, ha.star_eq]

/-- The support projection of a self-adjoint element of a W-star algebra. -/
noncomputable def support (a : selfAdjoint M) : {p : M // IsStarProjection p} :=
  leftSupport a.1

/-- The support projection acts as a left identity on its self-adjoint element. -/
@[simp]
theorem support_mul (a : selfAdjoint M) : (support a).1 * a.1 = a.1 :=
  leftSupport_mul a.1

/-- The support projection acts as a right identity on its self-adjoint element. -/
@[simp]
theorem mul_support (a : selfAdjoint M) : a.1 * (support a).1 = a.1 := by
  rw [support, IsSelfAdjoint.leftSupport_eq_rightSupport
    (selfAdjoint.isSelfAdjoint (x := a))]
  exact mul_rightSupport a.1

/-- Multiplication on the right by the support of a self-adjoint element has the same kernel as
multiplication on the right by that element. -/
theorem mul_support_eq_zero_iff (a : selfAdjoint M) (b : M) :
    b * (support a).1 = 0 ↔ b * a.1 = 0 :=
  mul_leftSupport_eq_zero_iff a.1 b

/-- Multiplication on the left by the support of a self-adjoint element has the same kernel as
multiplication on the left by that element. -/
theorem support_mul_eq_zero_iff (a : selfAdjoint M) (b : M) :
    (support a).1 * b = 0 ↔ a.1 * b = 0 := by
  rw [support, IsSelfAdjoint.leftSupport_eq_rightSupport a.property]
  exact rightSupport_mul_eq_zero_iff a.1 b

/-- A self-adjoint element restricted on the right to the support of its positive part equals its
positive part. -/
@[simp]
theorem mul_support_posPart (a : selfAdjoint M) :
    a.1 * (support ⟨a.1⁺, (CFC.posPart_nonneg a.1).isSelfAdjoint⟩).1 = a.1⁺ := by
  let aPos : selfAdjoint M := ⟨a.1⁺, (CFC.posPart_nonneg a.1).isSelfAdjoint⟩
  have hpos : a.1⁺ * (support aPos).1 = a.1⁺ := mul_support aPos
  have hneg : a.1⁻ * (support aPos).1 = 0 :=
    (mul_support_eq_zero_iff aPos a.1⁻).2 (CFC.negPart_mul_posPart a.1)
  calc
    a.1 * (support aPos).1 = (a.1⁺ - a.1⁻) * (support aPos).1 := by
      rw [CFC.posPart_sub_negPart a.1 a.property]
    _ = a.1⁺ := by rw [sub_mul, hpos, hneg, sub_zero]

/-- A self-adjoint element restricted on the left to the support of its positive part equals its
positive part. -/
@[simp]
theorem support_posPart_mul (a : selfAdjoint M) :
    (support ⟨a.1⁺, (CFC.posPart_nonneg a.1).isSelfAdjoint⟩).1 * a.1 = a.1⁺ := by
  let aPos : selfAdjoint M := ⟨a.1⁺, (CFC.posPart_nonneg a.1).isSelfAdjoint⟩
  have hpos : (support aPos).1 * a.1⁺ = a.1⁺ := support_mul aPos
  have hneg : (support aPos).1 * a.1⁻ = 0 :=
    (support_mul_eq_zero_iff aPos a.1⁻).2 (CFC.posPart_mul_negPart a.1)
  calc
    (support aPos).1 * a.1 = (support aPos).1 * (a.1⁺ - a.1⁻) := by
      rw [CFC.posPart_sub_negPart a.1 a.property]
    _ = a.1⁺ := by rw [mul_sub, hpos, hneg, sub_zero]

/-- The support of zero is zero. -/
@[simp]
theorem leftSupport_zero :
    leftSupport (0 : M) = ⟨0, IsStarProjection.zero M⟩ := by
  apply le_antisymm
  · exact (leftSupport_le_iff 0 ⟨0, IsStarProjection.zero M⟩).2 (zero_mul 0)
  · exact (leftSupport 0).2.nonneg

/-- The right support of zero is zero. -/
@[simp]
theorem rightSupport_zero :
    rightSupport (0 : M) = ⟨0, IsStarProjection.zero M⟩ := by
  rw [← leftSupport_star, star_zero, leftSupport_zero]

/-- The left support of one is one. -/
@[simp]
theorem leftSupport_one :
    leftSupport (1 : M) = ⟨1, IsStarProjection.one M⟩ := by
  apply Subtype.ext
  simpa only [mul_one] using leftSupport_mul (1 : M)

/-- The right support of one is one. -/
@[simp]
theorem rightSupport_one :
    rightSupport (1 : M) = ⟨1, IsStarProjection.one M⟩ := by
  rw [← leftSupport_star, star_one, leftSupport_one]

/-- Multiplication by a nonzero complex scalar does not change left support. -/
theorem leftSupport_smul (c : ℂ) (hc : c ≠ 0) (a : M) :
    leftSupport (c • a) = leftSupport a := by
  apply le_antisymm
  · rw [leftSupport_le_iff, mul_smul_comm, leftSupport_mul]
  · rw [leftSupport_le_iff]
    have h := leftSupport_mul (c • a)
    rw [mul_smul_comm] at h
    have hinv := congr_arg (c⁻¹ • ·) h
    simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hinv

/-- Multiplication by a nonzero complex scalar does not change right support. -/
theorem rightSupport_smul (c : ℂ) (hc : c ≠ 0) (a : M) :
    rightSupport (c • a) = rightSupport a := by
  apply le_antisymm
  · rw [rightSupport_le_iff, smul_mul_assoc, mul_rightSupport]
  · rw [rightSupport_le_iff]
    have h := mul_rightSupport (c • a)
    rw [smul_mul_assoc] at h
    have hinv := congr_arg (c⁻¹ • ·) h
    simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hinv

/-- Left support is monotone on nonnegative elements. -/
theorem leftSupport_mono_of_nonneg {a b : M} (ha : 0 ≤ a) (hab : a ≤ b) :
    leftSupport a ≤ leftSupport b := by
  rw [leftSupport_le_iff]
  exact (leftSupport b).2.mul_eq_self_of_nonneg_of_le_of_mul_eq_self
    ha hab (leftSupport_mul b)

/-- Right support is monotone on nonnegative elements. -/
theorem rightSupport_mono_of_nonneg {a b : M} (ha : 0 ≤ a) (hab : a ≤ b) :
    rightSupport a ≤ rightSupport b := by
  rw [← IsSelfAdjoint.leftSupport_eq_rightSupport (IsSelfAdjoint.of_nonneg ha),
    ← IsSelfAdjoint.leftSupport_eq_rightSupport (IsSelfAdjoint.of_nonneg (ha.trans hab))]
  exact leftSupport_mono_of_nonneg ha hab

/-- An element bounded below by a strictly positive real scalar has full left support. -/
theorem leftSupport_eq_one_of_algebraMap_le {a : M} {r : ℝ} (hr : 0 < r)
    (h : algebraMap ℝ M r ≤ a) :
    leftSupport a = ⟨1, IsStarProjection.one M⟩ := by
  have hmono := leftSupport_mono_of_nonneg (algebraMap_nonneg M hr.le) h
  have hscalar : leftSupport (algebraMap ℝ M r) = leftSupport (1 : M) := by
    rw [Algebra.algebraMap_eq_smul_one,
      RCLike.real_smul_eq_coe_smul (K := ℂ)]
    exact leftSupport_smul (r : ℂ) (Complex.ofReal_ne_zero.mpr hr.ne') 1
  apply le_antisymm
  · exact (leftSupport a).2.le_one
  · rw [← leftSupport_one, ← hscalar]
    exact hmono

/-- The internal identity of the nonunital ultraweak star algebra generated by a self-adjoint
element is its support projection. -/
theorem coe_unit_ultraweakAdjoin_singleton_eq_support
    (P : Type*) [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]
    (h : selfAdjoint M)
    [IsUnital (NonUnitalStarSubalgebra.ultraweakAdjoin (P := P) {h.1})] :
    ((IsUnital.isUnital.choose :
        NonUnitalStarSubalgebra.ultraweakAdjoin (P := P) {h.1}) : M) = (support h).1 := by
  let C := NonUnitalStarSubalgebra.ultraweakAdjoin (P := P) {h.1}
  let e : M := ((IsUnital.isUnital.choose : C) : M)
  have hhC : h.1 ∈ C :=
    NonUnitalStarSubalgebra.subset_ultraweakAdjoin (P := P) {h.1} (Set.mem_singleton h.1)
  have he : IsStarProjection e := IsUnital.isStarProjection_coe_unit C
  have heh : e * h.1 = h.1 := by
    exact congr_arg Subtype.val
      (IsUnital.isUnital.choose_spec (⟨h.1, hhC⟩ : C)).1
  have hse : support h ≤ (⟨e, he⟩ : {p : M // IsStarProjection p}) := by
    rw [support, leftSupport_le_iff]
    exact heh
  let T := IsStarProjection.Corner.nonUnitalStarSubalgebra (support h).2
  have hhT : h.1 ∈ T := by
    exact (Subsemigroup.mem_corner_iff (support h).2.isIdempotentElem).2
      ⟨support_mul h, mul_support h⟩
  have hCT : C ≤ T :=
    NonUnitalStarSubalgebra.ultraweakAdjoin_le (P := P)
      (fun x hx ↦ Set.mem_singleton_iff.mp hx ▸ hhT)
      (show T.IsUltraweakClosed (P := P) from inferInstance)
  have heC : e ∈ C := (IsUnital.isUnital.choose : C).property
  have heT : e ∈ T := hCT heC
  have hsupport_mul_e : (support h).1 * e = e :=
    (Subsemigroup.mem_corner_iff (support h).2.isIdempotentElem).mp heT |>.1
  have hsupport_mul_e' : (support h).1 * e = (support h).1 :=
    ((support h).2.le_iff_mul_eq_left he).mp hse
  exact hsupport_mul_e.symm.trans hsupport_mul_e'

/-- The support projection of a self-adjoint element belongs to the nonunital ultraweak star
algebra that it generates. -/
theorem support_mem_ultraweakAdjoin
    (P : Type*) [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]
    (h : selfAdjoint M) :
    (support h).1 ∈ NonUnitalStarSubalgebra.ultraweakAdjoin (P := P) {h.1} := by
  let C := NonUnitalStarSubalgebra.ultraweakAdjoin (P := P) {h.1}
  have hC : C.IsUltraweakClosed (P := P) :=
    NonUnitalStarSubalgebra.isUltraweakClosed_ultraweakAdjoin (P := P) {h.1}
  letI : NonUnitalCStarAlgebra C := hC.nonUnitalCStarAlgebra C
  letI : IsUnital C := hC.isUnital C
  rw [← coe_unit_ultraweakAdjoin_singleton_eq_support P h]
  exact (IsUnital.isUnital.choose : C).property

end WStarAlgebra
