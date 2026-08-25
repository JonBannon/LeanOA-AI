module

public import Mathlib.Algebra.Algebra.TransferInstance
public import Mathlib.Algebra.Star.TransferInstance
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
public import Mathlib.Analysis.CStarAlgebra.Projection
public import Mathlib.Analysis.Normed.Operator.Mul
public import LeanOA.PositiveContinuousLinearMap
public import Mathlib.Analysis.Normed.Ring.TransferInstance
public import LeanOA.Mathlib.RingTheory.Idempotents
public import LeanOA.Mathlib.Analysis.CStarAlgebra.Basic

@[expose] public section

/-!
# Corners of C⋆-algebras

This file analytically enriches Mathlib's algebraic corner `IsIdempotentElem.Corner` when the
distinguished idempotent is a star projection. The opaque synonym `IsStarProjection.Corner`
keeps the star, C⋆, and later W⋆ instances from leaking onto corners of arbitrary idempotents.
-/

namespace IsStarProjection

open scoped ComplexStarModule

universe u

/-- The corner cut out by a star projection, as an analytically extensible synonym of Mathlib's
algebraic corner associated to the underlying idempotent. -/
def Corner {A : Type u} [Semigroup A] [Star A] {p : A} (hp : IsStarProjection p) :=
  hp.isIdempotentElem.Corner

namespace Corner

variable {A : Type u} {p : A}

section Semigroup

variable [Semigroup A] [Star A] (hp : IsStarProjection p)

/-- The defining equivalence from a projection corner to Mathlib's algebraic idempotent corner. -/
def toIdempotentCorner : hp.Corner ≃ hp.isIdempotentElem.Corner := Equiv.refl _

/-- The ambient value of an element of a projection corner. -/
def val (x : hp.Corner) : A := (toIdempotentCorner hp x).1

instance : CoeOut hp.Corner A := ⟨val hp⟩

lemma val_injective : Function.Injective (val hp) := fun _ _ h ↦
  (toIdempotentCorner hp).injective <| Subtype.ext h

@[ext]
lemma ext {x y : hp.Corner} (h : (x : A) = y) : x = y := val_injective hp h

end Semigroup

section Semiring

variable [NonUnitalSemiring A] [Star A] (hp : IsStarProjection p)

instance : Semiring hp.Corner := (toIdempotentCorner hp).semiring

/-- The canonical ring equivalence from a projection corner to Mathlib's algebraic idempotent
corner. -/
def toIdempotentCornerRingEquiv : hp.Corner ≃+* hp.isIdempotentElem.Corner :=
  { toIdempotentCorner hp with
    map_add' := fun _ _ ↦ rfl
    map_mul' := fun _ _ ↦ rfl }

@[simp]
lemma toIdempotentCornerRingEquiv_apply (x : hp.Corner) :
    toIdempotentCornerRingEquiv hp x = toIdempotentCorner hp x := rfl

@[simp]
lemma toIdempotentCornerRingEquiv_symm_apply (x : hp.isIdempotentElem.Corner) :
    (toIdempotentCornerRingEquiv hp).symm x = (toIdempotentCorner hp).symm x := rfl

@[simp]
lemma coe_zero : ((0 : hp.Corner) : A) = 0 := rfl

@[simp]
lemma coe_one : ((1 : hp.Corner) : A) = p := rfl

@[simp]
lemma coe_add (x y : hp.Corner) : ((x + y : hp.Corner) : A) = x + y := rfl

@[simp]
lemma coe_mul (x y : hp.Corner) : ((x * y : hp.Corner) : A) = x * y := rfl

@[simp]
lemma projection_mul (x : hp.Corner) : p * (x : A) = x :=
  (Subsemigroup.mem_corner_iff hp.isIdempotentElem).mp
    (toIdempotentCorner hp x).property |>.1

@[simp]
lemma mul_projection (x : hp.Corner) : (x : A) * p = x :=
  (Subsemigroup.mem_corner_iff hp.isIdempotentElem).mp
    (toIdempotentCorner hp x).property |>.2

end Semiring

section CommSemiring

variable [NonUnitalCommSemiring A] [Star A] (hp : IsStarProjection p)

instance : CommSemiring hp.Corner := (toIdempotentCorner hp).commSemiring

end CommSemiring

section Ring

variable [NonUnitalRing A] [Star A] (hp : IsStarProjection p)

instance : Ring hp.Corner := (toIdempotentCorner hp).ring

@[simp]
lemma coe_neg (x : hp.Corner) : ((-x : hp.Corner) : A) = -x := rfl

@[simp]
lemma coe_sub (x y : hp.Corner) : ((x - y : hp.Corner) : A) = x - y := rfl

end Ring

section CommRing

variable [NonUnitalCommRing A] [Star A] (hp : IsStarProjection p)

instance : CommRing hp.Corner := (toIdempotentCorner hp).commRing

end CommRing

section StarAlgebra

variable [NonUnitalRing A] [Module ℂ A] [StarRing A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  (hp : IsStarProjection p)

/-- The corner as a nonunital star subalgebra of its ambient algebra. This is an internal
realization of the carrier; its multiplicative identity as a corner is `p`, not the ambient `1`. -/
def nonUnitalStarSubalgebra : NonUnitalStarSubalgebra ℂ A where
  __ := NonUnitalRing.corner p
  smul_mem' := by
    rintro c _ ⟨a, rfl⟩
    exact ⟨c • a, by simp only [mul_smul_comm, smul_mul_assoc]⟩
  star_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨star a, by simp only [star_mul, hp.isSelfAdjoint.star_eq, mul_assoc]⟩

/-- A projection corner is canonically equivalent to its realization as a nonunital star
subalgebra of the ambient algebra. -/
def toNonUnitalStarSubalgebra : hp.Corner ≃ nonUnitalStarSubalgebra hp := by
  refine
    { toFun := fun x ↦ ⟨val hp x, (toIdempotentCorner hp x).property⟩
      invFun := fun x ↦ (toIdempotentCorner hp).symm ⟨x, x.property⟩
      left_inv := fun x ↦ ?_
      right_inv := fun x ↦ ?_ }
  · exact (toIdempotentCorner hp).injective <| Subtype.ext rfl
  · exact Subtype.ext <| congr_arg Subtype.val <| (toIdempotentCorner hp).apply_symm_apply _

@[simp]
lemma coe_toNonUnitalStarSubalgebra (x : hp.Corner) :
    ((toNonUnitalStarSubalgebra hp x : nonUnitalStarSubalgebra hp) : A) = x := rfl

@[simp]
lemma coe_toNonUnitalStarSubalgebra_symm (x : nonUnitalStarSubalgebra hp) :
    (((toNonUnitalStarSubalgebra hp).symm x : hp.Corner) : A) = x := rfl

instance : Module ℂ hp.Corner := Equiv.module ℂ (toNonUnitalStarSubalgebra hp)

instance : Star hp.Corner := Equiv.star (toNonUnitalStarSubalgebra hp)

@[simp]
lemma coe_smul (c : ℂ) (x : hp.Corner) : ((c • x : hp.Corner) : A) = c • x := rfl

@[simp]
lemma coe_star (x : hp.Corner) : ((star x : hp.Corner) : A) = star (x : A) := rfl

instance : StarRing hp.Corner :=
  Function.Injective.starRing (f := val hp) (val_injective hp)
    (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

instance [StarModule ℂ A] : StarModule ℂ hp.Corner :=
  Function.Injective.starModule (f := val hp) ℂ (val_injective hp)
    (fun _ ↦ rfl) (fun _ _ ↦ rfl)

noncomputable instance : Algebra ℂ hp.Corner := Algebra.ofModule
  (fun c x y ↦ ext hp <| by simp [smul_mul_assoc])
  (fun c x y ↦ ext hp <| by simp [mul_smul_comm])

@[simp]
lemma coe_algebraMap (c : ℂ) : ((algebraMap ℂ hp.Corner c : hp.Corner) : A) = c • p := by
  rw [Algebra.algebraMap_eq_smul_one, coe_smul, coe_one]

/-- The canonical star-algebra equivalence from a projection corner to its realization as a
nonunital star subalgebra of the ambient algebra. -/
def toNonUnitalStarSubalgebraStarAlgEquiv :
    hp.Corner ≃⋆ₐ[ℂ] nonUnitalStarSubalgebra hp :=
  { toNonUnitalStarSubalgebra hp with
    map_add' := fun _ _ ↦ Subtype.ext rfl
    map_mul' := fun _ _ ↦ Subtype.ext rfl
    map_smul' := fun _ _ ↦ Subtype.ext rfl
    map_star' := fun _ ↦ Subtype.ext rfl }

@[simp]
lemma toNonUnitalStarSubalgebraStarAlgEquiv_apply (x : hp.Corner) :
    toNonUnitalStarSubalgebraStarAlgEquiv hp x = toNonUnitalStarSubalgebra hp x := rfl

@[simp]
lemma toNonUnitalStarSubalgebraStarAlgEquiv_symm_apply
    (x : nonUnitalStarSubalgebra hp) :
    (toNonUnitalStarSubalgebraStarAlgEquiv hp).symm x =
      (toNonUnitalStarSubalgebra hp).symm x := rfl

/-- The inclusion of a corner into its ambient algebra as a nonunital star-algebra homomorphism. -/
def inclusion : hp.Corner →⋆ₙₐ[ℂ] A where
  toFun := val hp
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

@[simp]
lemma inclusion_apply (x : hp.Corner) : inclusion hp x = x := rfl

/-- The ambient linear subspace underlying a projection corner. -/
def rangeSubmodule : Submodule ℂ A :=
  (nonUnitalStarSubalgebra hp).toNonUnitalSubalgebra.toSubmodule

@[simp]
lemma mem_rangeSubmodule_iff (x : A) :
    x ∈ rangeSubmodule hp ↔ p * x = x ∧ x * p = x :=
  Subsemigroup.mem_corner_iff hp.isIdempotentElem

@[simp]
lemma coe_realPart [StarModule ℂ A] (x : hp.Corner) :
    (((ℜ x : selfAdjoint hp.Corner) : hp.Corner) : A) =
      ((ℜ (x : A) : selfAdjoint A) : A) := by
  rw [realPart_apply_coe, realPart_apply_coe]
  change inclusion hp ((2 : ℝ)⁻¹ • (x + star x)) =
    (2 : ℝ)⁻¹ • (inclusion hp x + star (inclusion hp x))
  rw [LinearMapClass.map_smul_of_tower]
  simp

@[simp]
lemma coe_imaginaryPart [StarModule ℂ A] (x : hp.Corner) :
    (((ℑ x : selfAdjoint hp.Corner) : hp.Corner) : A) =
      ((ℑ (x : A) : selfAdjoint A) : A) := by
  rw [imaginaryPart_apply_coe, imaginaryPart_apply_coe]
  change inclusion hp (-Complex.I • (2 : ℝ)⁻¹ • (x - star x)) =
    -Complex.I • (2 : ℝ)⁻¹ • (inclusion hp x - star (inclusion hp x))
  rw [map_smul, LinearMapClass.map_smul_of_tower]
  simp

end StarAlgebra

section NonUnitalCStarAlgebra

variable [NonUnitalCStarAlgebra A] (hp : IsStarProjection p)

lemma isClosed_carrier : IsClosed (nonUnitalStarSubalgebra hp : Set A) := by
  rw [show (nonUnitalStarSubalgebra hp : Set A) =
      {x | p * x = x} ∩ {x | x * p = x} by
    ext x
    exact Subsemigroup.mem_corner_iff hp.isIdempotentElem]
  exact (isClosed_eq (continuous_const.mul continuous_id) continuous_id).inter
    (isClosed_eq (continuous_id.mul continuous_const) continuous_id)

instance : IsClosed (nonUnitalStarSubalgebra hp : Set A) := isClosed_carrier hp

noncomputable instance : NormedRing hp.Corner where
  __ : NonUnitalNormedRing hp.Corner :=
    NonUnitalNormedRing.induced hp.Corner A
      (inclusion hp).toNonUnitalAlgHom (val_injective hp)
  __ : Ring hp.Corner := inferInstance

noncomputable instance : NormedAlgebra ℂ hp.Corner where
  __ : Algebra ℂ hp.Corner := inferInstance
  norm_smul_le c x := by
    change ‖c • (x : A)‖ ≤ ‖c‖ * ‖(x : A)‖
    exact norm_smul_le c (x : A)

@[simp]
lemma norm_coe (x : hp.Corner) : ‖(x : A)‖ = ‖x‖ := rfl

/-- The explicit linear isometry between a projection corner and its ambient range submodule. -/
noncomputable def toRangeSubmoduleₗᵢ : hp.Corner ≃ₗᵢ[ℂ] rangeSubmodule hp where
  toFun x := ⟨x, (toNonUnitalStarSubalgebra hp x).property⟩
  invFun x := (toNonUnitalStarSubalgebra hp).symm
    ⟨x.1, x.property⟩
  left_inv _ := (toNonUnitalStarSubalgebra hp).injective <| Subtype.ext rfl
  right_inv x := Subtype.ext <| congr_arg Subtype.val <|
    (toNonUnitalStarSubalgebra hp).apply_symm_apply ⟨x.1, x.property⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl
  norm_map' _ := rfl

@[simp]
lemma coe_toRangeSubmoduleₗᵢ (x : hp.Corner) :
    ((toRangeSubmoduleₗᵢ hp x : rangeSubmodule hp) : A) = x := rfl

@[simp]
lemma coe_toRangeSubmoduleₗᵢ_symm (x : rangeSubmodule hp) :
    (((toRangeSubmoduleₗᵢ hp).symm x : hp.Corner) : A) = x := rfl

@[simp]
lemma dist_coe (x y : hp.Corner) : dist (x : A) y = dist x y := rfl

/-- The ambient-value map of a projection corner is an isometry. -/
lemma isometry_val : Isometry (val hp) := fun _ _ ↦ rfl

/-- The norm-continuous linear inclusion of a projection corner into its ambient C⋆-algebra. -/
noncomputable def inclusionL : hp.Corner →L[ℂ] A where
  toFun := val hp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := (isometry_val hp).continuous

@[simp]
lemma inclusionL_apply (x : hp.Corner) : inclusionL hp x = x := rfl

@[simp]
lemma coe_algebraMap_real (r : ℝ) :
    ((algebraMap ℝ hp.Corner r : hp.Corner) : A) = (r : ℂ) • p := by
  rw [Algebra.algebraMap_eq_smul_one]
  change inclusionL hp (r • (1 : hp.Corner)) = (r : ℂ) • p
  rw [LinearMapClass.map_smul_of_tower]
  simp

/-- The norm-continuous cutdown map from a C⋆-algebra to a projection corner. -/
noncomputable def cutdownL : A →L[ℂ] hp.Corner where
  toFun x := (toNonUnitalStarSubalgebra hp).symm ⟨p * x * p, ⟨x, rfl⟩⟩
  map_add' x y := ext hp <| by simp [mul_add, add_mul]
  map_smul' c x := ext hp <| by simp [mul_smul_comm, smul_mul_assoc]
  cont := by
    rw [(isometry_val hp).isEmbedding.continuous_iff]
    exact (continuous_const.mul continuous_id).mul continuous_const

@[simp]
lemma coe_cutdownL (x : A) : (cutdownL hp x : A) = p * x * p := rfl

@[simp]
lemma cutdownL_inclusionL (x : hp.Corner) : cutdownL hp (x : A) = x := by
  ext
  simp

@[simp]
lemma inclusionL_cutdownL (x : A) : inclusionL hp (cutdownL hp x) = p * x * p := rfl

/-- Cutting down by a projection is contractive. -/
lemma norm_cutdownL_le (x : A) : ‖cutdownL hp x‖ ≤ ‖x‖ := by
  rw [← norm_coe hp, coe_cutdownL]
  calc
    ‖p * x * p‖ ≤ ‖p‖ * ‖x‖ * ‖p‖ :=
      (norm_mul_le ..).trans <|
        mul_le_mul_of_nonneg_right (norm_mul_le ..) (norm_nonneg _)
    _ ≤ 1 * ‖x‖ * 1 := by
      gcongr <;> exact IsStarProjection.norm_le p hp
    _ = ‖x‖ := by simp

lemma cutdownL_surjective : Function.Surjective (cutdownL hp) := fun x ↦
  ⟨inclusionL hp x, by simp⟩

noncomputable instance : CompleteSpace hp.Corner := by
  letI : NonUnitalCStarAlgebra (nonUnitalStarSubalgebra hp) := inferInstance
  let e : hp.Corner ≃ᵢ nonUnitalStarSubalgebra hp :=
    { toEquiv := toNonUnitalStarSubalgebra hp
      isometry_toFun _ _ := rfl }
  exact e.completeSpace

instance : CStarRing hp.Corner where
  norm_mul_self_le x := by
    change ‖(x : A)‖ * ‖(x : A)‖ ≤ ‖star (x : A) * (x : A)‖
    exact CStarRing.norm_mul_self_le (x := (x : A))

noncomputable instance : CStarAlgebra hp.Corner where

noncomputable instance [PartialOrder A] : PartialOrder hp.Corner :=
  PartialOrder.lift (val hp) (val_injective hp)

@[simp]
lemma coe_le [PartialOrder A] (x y : hp.Corner) : x ≤ y ↔ (x : A) ≤ (y : A) := Iff.rfl

@[simp]
lemma coe_lt [PartialOrder A] (x y : hp.Corner) : x < y ↔ (x : A) < (y : A) := Iff.rfl

noncomputable instance [PartialOrder A] [StarOrderedRing A] : StarOrderedRing hp.Corner := by
  refine .of_nonneg_iff' (fun {x y} h z ↦ ?_) fun x ↦ ⟨fun hx ↦ ?_, ?_⟩
  · change (x : A) ≤ y at h
    change (z : A) + x ≤ (z : A) + y
    exact add_le_add_right h _
  · let r : A := CFC.sqrt (x : A)
    have hr : r ∈ nonUnitalStarSubalgebra hp := by
      simp only [r, CFC.sqrt, cfcₙ_nnreal_eq_real _ (x : A) hx]
      exact cfcₙ_mem _ (toNonUnitalStarSubalgebra hp x).property
    let y : hp.Corner := (toNonUnitalStarSubalgebra hp).symm ⟨r, hr⟩
    refine ⟨y, ext hp ?_⟩
    simp [r, y, (CFC.sqrt_nonneg (x : A)).star_eq, CFC.sqrt_mul_sqrt_self (x : A)]
  · rintro ⟨x, rfl⟩
    exact star_mul_self_nonneg (x : A)

section Order

variable [PartialOrder A]

/-- The positive norm-continuous inclusion of a projection corner into its ambient
C-star algebra. -/
noncomputable def inclusionP : hp.Corner →P[ℂ] A where
  toFun := val hp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  monotone' _ _ := id
  cont := (inclusionL hp).continuous

@[simp]
lemma inclusionP_apply (x : hp.Corner) : inclusionP hp x = x := rfl

variable [StarOrderedRing A]

/-- The positive norm-continuous cutdown from a C-star algebra to a projection corner. -/
noncomputable def cutdownP : A →P[ℂ] hp.Corner where
  toFun := cutdownL hp
  map_add' := map_add (cutdownL hp)
  map_smul' := map_smul (cutdownL hp)
  monotone' x y h := by
    change p * x * p ≤ p * y * p
    simpa only [hp.isSelfAdjoint.star_eq] using star_left_conjugate_le_conjugate h p
  cont := (cutdownL hp).continuous

@[simp]
lemma cutdownP_apply (x : A) : cutdownP hp x = cutdownL hp x := rfl

end Order

end NonUnitalCStarAlgebra

section NonUnitalCommCStarAlgebra

variable [NonUnitalCommCStarAlgebra A] (hp : IsStarProjection p)

noncomputable instance : CommCStarAlgebra hp.Corner where

end NonUnitalCommCStarAlgebra

end Corner

section OffDiagonal

variable {A : Type*} [CStarAlgebra A] {p : A}

/-- An off-diagonal Peirce component is contractive. -/
lemma norm_mul_one_sub_le (hp : IsStarProjection p) (a : A) :
    ‖p * a * (1 - p)‖ ≤ ‖a‖ := by
  calc
    ‖p * a * (1 - p)‖ ≤ ‖p‖ * ‖a‖ * ‖1 - p‖ :=
      (norm_mul_le ..).trans <|
        mul_le_mul_of_nonneg_right (norm_mul_le ..) (norm_nonneg _)
    _ ≤ 1 * ‖a‖ * 1 := by
      gcongr
      · exact IsStarProjection.norm_le p hp
      · exact IsStarProjection.norm_le (1 - p) hp.one_sub
    _ = ‖a‖ := by simp

/-- Upper and lower off-diagonal Peirce components have max norm under addition. -/
lemma norm_mul_one_sub_add_smul_one_sub_mul_eq_max (hp : IsStarProjection p)
    (a b : A) (z : ℂ) :
    ‖p * a * (1 - p) + z • ((1 - p) * b * p)‖ =
      max ‖p * a * (1 - p)‖ (‖z‖ * ‖(1 - p) * b * p‖) := by
  rw [CStarRing.norm_add_eq_max_of_mul_star_eq_zero_of_star_mul_eq_zero]
  · simp [norm_smul]
  · rw [star_smul, mul_smul_comm,
      show star ((1 - p) * b * p) = p * star b * (1 - p) by
        simp [star_mul, hp.isSelfAdjoint.star_eq,
          hp.one_sub.isSelfAdjoint.star_eq, mul_assoc]]
    rw [show p * a * (1 - p) * (p * star b * (1 - p)) = 0 by
      calc
        _ = p * a * ((1 - p) * p) * star b * (1 - p) := by noncomm_ring
        _ = 0 := by rw [hp.one_sub_mul_self]; simp]
    simp
  · rw [show star (p * a * (1 - p)) = (1 - p) * star a * p by
      simp [star_mul, hp.isSelfAdjoint.star_eq,
        hp.one_sub.isSelfAdjoint.star_eq, mul_assoc], mul_smul_comm]
    apply smul_eq_zero.mpr
    refine Or.inr ?_
    calc
      (1 - p) * star a * p * ((1 - p) * b * p) =
          (1 - p) * star a * (p * (1 - p)) * b * p := by noncomm_ring
      _ = 0 := by rw [hp.mul_one_sub_self]; simp

/-- An off-diagonal Peirce component is square-zero. -/
lemma mul_one_sub_mul_self_eq_zero (hp : IsStarProjection p) (a : A) :
    (p * a * (1 - p)) * (p * a * (1 - p)) = 0 := by
  calc
    (p * a * (1 - p)) * (p * a * (1 - p)) =
        p * a * ((1 - p) * p) * a * (1 - p) := by noncomm_ring
    _ = 0 := by rw [hp.one_sub_mul_self]; simp

/-- The self-adjoint dilation of an upper off-diagonal Peirce component cuts back down to that
component. -/
lemma mul_add_star_mul_one_sub (hp : IsStarProjection p) (a : A) :
    p * (p * a * (1 - p) + star (p * a * (1 - p))) * (1 - p) =
      p * a * (1 - p) := by
  rw [mul_add, add_mul]
  calc
    p * (p * a * (1 - p)) * (1 - p) +
        p * star (p * a * (1 - p)) * (1 - p) =
        (p * p) * a * ((1 - p) * (1 - p)) +
          (p * (1 - p)) * star a * p * (1 - p) := by
      simp only [star_mul, hp.isSelfAdjoint.star_eq,
        hp.one_sub.isSelfAdjoint.star_eq]
      noncomm_ring
    _ = p * a * (1 - p) := by
      rw [hp.isIdempotentElem.eq, hp.one_sub.isIdempotentElem.eq,
        hp.mul_one_sub_self]
      simp

/-- Every upper off-diagonal Peirce component has a self-adjoint dilation of the same norm. -/
lemma exists_isSelfAdjoint_norm_eq_mul_one_sub (hp : IsStarProjection p) (a : A) :
    ∃ x : A, IsSelfAdjoint x ∧ ‖x‖ = ‖p * a * (1 - p)‖ ∧
      p * x * (1 - p) = p * a * (1 - p) := by
  exact ⟨p * a * (1 - p) + star (p * a * (1 - p)),
    by simp [isSelfAdjoint_iff, add_comm],
    CStarRing.norm_add_star_of_mul_self_eq_zero (hp.mul_one_sub_mul_self_eq_zero a),
    hp.mul_add_star_mul_one_sub a⟩

end OffDiagonal

end IsStarProjection
