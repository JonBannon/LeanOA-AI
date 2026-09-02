module

public import LeanOA.Ultraweak.IsUnital
public import LeanOA.Ultraweak.StarSubalgebra
public import Mathlib.Topology.Algebra.NonUnitalStarAlgebra

@[expose] public section

/-!
# Ultraweakly closed nonunital star subalgebras

This file supplies the nonunital analogue of `StarSubalgebra.ultraweakClosure`. The algebraic
carrier remains independent of a chosen predual, while closedness is recorded relative to a
specified predual.
-/

open Set
open scoped Ultraweak

namespace Ultraweak

variable {M P : Type*} [CStarAlgebra M]
  [NormedAddCommGroup P] [NormedSpace ℂ P] [Predual ℂ M P]

/-- A nonunital star subalgebra transported explicitly to the ultraweak copy of its ambient
algebra. -/
noncomputable def ofNonUnitalStarSubalgebra (S : NonUnitalStarSubalgebra ℂ M) :
    NonUnitalStarSubalgebra ℂ σ(M, P) :=
  S.comap (starAlgEquiv M P).toNonUnitalStarAlgHom

@[simp]
lemma mem_ofNonUnitalStarSubalgebra (S : NonUnitalStarSubalgebra ℂ M) (x : σ(M, P)) :
    x ∈ ofNonUnitalStarSubalgebra (P := P) S ↔ ofUltraweak x ∈ S :=
  Iff.rfl

@[simp]
lemma ofNonUnitalStarSubalgebra_toSubmodule (S : NonUnitalStarSubalgebra ℂ M) :
    (ofNonUnitalStarSubalgebra (P := P) S).toSubmodule =
      ofSubmodule (P := P) S.toSubmodule := by
  ext
  simp

end Ultraweak

namespace NonUnitalStarSubalgebra

section CarrierEquiv

variable {𝕜 A : Type*} [CommRing 𝕜]
  [NonUnitalSeminormedRing A] [Module 𝕜 A] [Star A]

/-- The canonical linear isometry between a nonunital star subalgebra and the ambient submodule
with the same carrier. -/
def toSubmoduleLinearIsometryEquiv (S : NonUnitalStarSubalgebra 𝕜 A) :
    S ≃ₗᵢ[𝕜] S.toSubmodule :=
  { S.toNonUnitalSubalgebra.toSubmoduleEquiv.symm with
    norm_map' := fun _ ↦ rfl }

@[simp]
lemma coe_toSubmoduleLinearIsometryEquiv_apply
    (S : NonUnitalStarSubalgebra 𝕜 A) (x : S) :
    ((toSubmoduleLinearIsometryEquiv S x : S.toSubmodule) : A) = x :=
  rfl

@[simp]
lemma coe_toSubmoduleLinearIsometryEquiv_symm_apply
    (S : NonUnitalStarSubalgebra 𝕜 A) (x : S.toSubmodule) :
    ((toSubmoduleLinearIsometryEquiv S).symm x : A) = x :=
  rfl

end CarrierEquiv

variable {M P : Type*} [CStarAlgebra M]
  [NormedAddCommGroup P] [NormedSpace ℂ P] [Predual ℂ M P]

/-- Compatibility class asserting that a nonunital star subalgebra is closed in the ultraweak
topology specified by `P`. -/
class IsUltraweakClosed (S : NonUnitalStarSubalgebra ℂ M) : Prop where
  /-- The underlying submodule, transported to the specified ultraweak topology, is closed. -/
  isClosed :
    IsClosed (Ultraweak.ofSubmodule (P := P) S.toSubmodule : Set σ(M, P))

namespace IsUltraweakClosed

variable {S : NonUnitalStarSubalgebra ℂ M}

/-- An ultraweakly closed nonunital star subalgebra is norm closed. -/
theorem norm_isClosed (hS : S.IsUltraweakClosed (P := P)) : IsClosed (S : Set M) := by
  convert hS.isClosed.preimage (continuous_toUltraweak (M := M) (P := P)) using 1
  ext x
  simp

/-- Ultraweak closedness of a nonunital star subalgebra, expressed as closedness of its ambient
carrier preimage. -/
lemma isClosed_ambientPreimage (hS : S.IsUltraweakClosed (P := P)) :
    IsClosed (ofUltraweak ⁻¹' (S : Set M) : Set σ(M, P)) := by
  convert hS.isClosed using 1
  ext x
  simp

/-- The quotient predual induced on an ultraweakly closed nonunital star subalgebra by an
explicitly specified ambient predual. -/
@[implicit_reducible]
noncomputable def inducedPredual (S : NonUnitalStarSubalgebra ℂ M)
    (hS : S.IsUltraweakClosed (P := P)) :
    Predual ℂ S (P ⧸ Ultraweak.preannihilator (P := P) S.toSubmodule) := by
  letI : Predual ℂ S.toSubmodule
      (P ⧸ Ultraweak.preannihilator (P := P) S.toSubmodule) :=
    Ultraweak.closedSubmodulePredual (P := P) S.toSubmodule hS.isClosed
  exact Predual.congr (toSubmoduleLinearIsometryEquiv S)

/-- Evaluation for the quotient predual induced on a closed nonunital star subalgebra agrees
with ambient evaluation on representatives. -/
@[simp]
theorem inducedPredual_equivDual_apply_mk (S : NonUnitalStarSubalgebra ℂ M)
    (hS : S.IsUltraweakClosed (P := P)) (x : S) (p : P) :
    Predual.equivDual (𝕜 := ℂ) (M := S)
        (P := P ⧸ Ultraweak.preannihilator (P := P) S.toSubmodule)
        (self := inducedPredual S hS) x
        (Submodule.Quotient.mk p :
          P ⧸ Ultraweak.preannihilator (P := P) S.toSubmodule) =
      Predual.equivDual (𝕜 := ℂ) (M := M) (P := P) x.1 p := by
  change Ultraweak.closedSubmoduleEquivDual (P := P) S.toSubmodule hS.isClosed
      (toSubmoduleLinearIsometryEquiv S x) (Submodule.Quotient.mk p) = _
  exact Ultraweak.closedSubmoduleEquivDual_apply_mk
    S.toSubmodule hS.isClosed (toSubmoduleLinearIsometryEquiv S x) p

/-- The intrinsic ultraweak topology on a closed nonunital star subalgebra agrees with the
intrinsic quotient-predual topology on its submodule presentation. -/
noncomputable def inducedUltraweakEquivSubmodule (S : NonUnitalStarSubalgebra ℂ M)
    (hS : S.IsUltraweakClosed (P := P)) :
    @Ultraweak ℂ S
        (P ⧸ Ultraweak.preannihilator (P := P) S.toSubmodule)
        _ _ _ _ _ (inducedPredual S hS) ≃L[ℂ]
      @Ultraweak ℂ S.toSubmodule
        (P ⧸ Ultraweak.preannihilator (P := P) S.toSubmodule)
        _ _ _ _ _ (Ultraweak.closedSubmodulePredual
          (P := P) S.toSubmodule hS.isClosed) := by
  letI : Predual ℂ S
      (P ⧸ Ultraweak.preannihilator (P := P) S.toSubmodule) :=
    inducedPredual S hS
  letI : Predual ℂ S.toSubmodule
      (P ⧸ Ultraweak.preannihilator (P := P) S.toSubmodule) :=
    Ultraweak.closedSubmodulePredual (P := P) S.toSubmodule hS.isClosed
  exact WeakBilin.congr _ (toSubmoduleLinearIsometryEquiv S).toLinearEquiv
    (LinearEquiv.refl ℂ _) _ rfl

@[simp]
lemma inducedUltraweakEquivSubmodule_apply (S : NonUnitalStarSubalgebra ℂ M)
    (hS : S.IsUltraweakClosed (P := P))
    (x : @Ultraweak ℂ S
      (P ⧸ Ultraweak.preannihilator (P := P) S.toSubmodule)
      _ _ _ _ _ (inducedPredual S hS)) :
    (show S.toSubmodule from inducedUltraweakEquivSubmodule S hS x) =
      toSubmoduleLinearIsometryEquiv S (show S from x) :=
  rfl

@[simp]
lemma inducedUltraweakEquivSubmodule_symm_apply (S : NonUnitalStarSubalgebra ℂ M)
    (hS : S.IsUltraweakClosed (P := P))
    (x : @Ultraweak ℂ S.toSubmodule
      (P ⧸ Ultraweak.preannihilator (P := P) S.toSubmodule)
      _ _ _ _ _ (Ultraweak.closedSubmodulePredual
        (P := P) S.toSubmodule hS.isClosed)) :
    (show S from (inducedUltraweakEquivSubmodule S hS).symm x) =
      (toSubmoduleLinearIsometryEquiv S).symm (show S.toSubmodule from x) :=
  rfl

/-- The intrinsic quotient-predual ultraweak topology on a closed nonunital star subalgebra is
the ambient ultraweak subspace topology. -/
noncomputable def inducedAmbientUltraweakEquiv (S : NonUnitalStarSubalgebra ℂ M)
    (hS : S.IsUltraweakClosed (P := P)) :
    @Ultraweak ℂ S
        (P ⧸ Ultraweak.preannihilator (P := P) S.toSubmodule)
        _ _ _ _ _ (inducedPredual S hS) ≃L[ℂ]
      Ultraweak.ofSubmodule (P := P) S.toSubmodule :=
  (hS.inducedUltraweakEquivSubmodule S).trans
    (Ultraweak.closedSubmoduleUltraweakEquiv (P := P) S.toSubmodule hS.isClosed)

@[simp]
lemma inducedAmbientUltraweakEquiv_apply (S : NonUnitalStarSubalgebra ℂ M)
    (hS : S.IsUltraweakClosed (P := P))
    (x : @Ultraweak ℂ S
      (P ⧸ Ultraweak.preannihilator (P := P) S.toSubmodule)
      _ _ _ _ _ (inducedPredual S hS)) :
    (inducedAmbientUltraweakEquiv S hS x).1 = toUltraweak ℂ P x.1 :=
  rfl

@[simp]
lemma inducedAmbientUltraweakEquiv_symm_apply (S : NonUnitalStarSubalgebra ℂ M)
    (hS : S.IsUltraweakClosed (P := P))
    (x : Ultraweak.ofSubmodule (P := P) S.toSubmodule) :
    (show S from (inducedAmbientUltraweakEquiv S hS).symm x) =
      ⟨ofUltraweak x.1,
        Ultraweak.mem_ofSubmodule S.toSubmodule x.1 |>.mp x.2⟩ :=
  rfl

end IsUltraweakClosed

section Closure

variable [PartialOrder M] [StarOrderedRing M] [CompleteSpace P]

/-- The ultraweak closure of a nonunital star subalgebra, retained as an ordinary nonunital star
subalgebra of `M`. -/
noncomputable def ultraweakClosure (S : NonUnitalStarSubalgebra ℂ M) :
    NonUnitalStarSubalgebra ℂ M :=
  (Ultraweak.ofNonUnitalStarSubalgebra (P := P) S).topologicalClosure.comap
    (Ultraweak.starAlgEquiv M P).symm.toNonUnitalStarAlgHom

@[simp]
lemma mem_ultraweakClosure (S : NonUnitalStarSubalgebra ℂ M) (x : M) :
    x ∈ S.ultraweakClosure (P := P) ↔
      toUltraweak ℂ P x ∈
        closure (Ultraweak.ofNonUnitalStarSubalgebra (P := P) S : Set σ(M, P)) :=
  Iff.rfl

theorem le_ultraweakClosure (S : NonUnitalStarSubalgebra ℂ M) :
    S ≤ S.ultraweakClosure (P := P) :=
  fun x hx ↦ by
    rw [mem_ultraweakClosure]
    exact subset_closure <| by
      change ofUltraweak (toUltraweak ℂ P x) ∈ S
      simpa using hx

instance (S : NonUnitalStarSubalgebra ℂ M) :
    IsUltraweakClosed (P := P) (S.ultraweakClosure (P := P)) where
  isClosed := by
    rw [← Ultraweak.ofNonUnitalStarSubalgebra_toSubmodule]
    convert NonUnitalStarSubalgebra.isClosed_topologicalClosure
      (Ultraweak.ofNonUnitalStarSubalgebra (P := P) S) using 1
    ext x
    rfl

theorem ultraweakClosure_minimal {S T : NonUnitalStarSubalgebra ℂ M}
    (hST : S ≤ T) (hT : T.IsUltraweakClosed (P := P)) :
    S.ultraweakClosure (P := P) ≤ T := by
  intro x hx
  rw [mem_ultraweakClosure] at hx
  have : toUltraweak ℂ P x ∈ Ultraweak.ofNonUnitalStarSubalgebra (P := P) T :=
    closure_minimal (fun y hy ↦ by simpa using hST <| by simpa using hy) hT.isClosed hx
  simpa using this

@[simp]
theorem ultraweakClosure_eq_self {S : NonUnitalStarSubalgebra ℂ M}
    [S.IsUltraweakClosed (P := P)] : S.ultraweakClosure (P := P) = S :=
  le_antisymm (ultraweakClosure_minimal le_rfl inferInstance) (le_ultraweakClosure S)

/-- Ultraweak closure preserves commutativity. -/
instance (S : NonUnitalStarSubalgebra ℂ M) [hS : IsMulCommutative S] :
    IsMulCommutative (S.ultraweakClosure (P := P)) := by
  let T := Ultraweak.ofNonUnitalStarSubalgebra (P := P) S
  have hT : IsMulCommutative T := .of_setLike_mul_comm fun x hx y hy ↦ by
    rw [← ofUltraweak_inj, Ultraweak.ofUltraweak_mul, Ultraweak.ofUltraweak_mul]
    exact setLike_mul_comm
      (Ultraweak.mem_ofNonUnitalStarSubalgebra (P := P) S x |>.mp hx)
      (Ultraweak.mem_ofNonUnitalStarSubalgebra (P := P) S y |>.mp hy)
  letI : NonUnitalCommRing T.topologicalClosure :=
    NonUnitalStarSubalgebra.nonUnitalCommRingTopologicalClosure T hT.is_comm.comm
  refine .of_setLike_mul_comm fun x hx y hy ↦ ?_
  let x' : T.topologicalClosure := ⟨toUltraweak ℂ P x, hx⟩
  let y' : T.topologicalClosure := ⟨toUltraweak ℂ P y, hy⟩
  apply (toUltraweak_inj (𝕜 := ℂ) (P := P)).mp
  rw [Ultraweak.toUltraweak_mul, Ultraweak.toUltraweak_mul]
  exact congr_arg Subtype.val (mul_comm x' y')

/-- The smallest ultraweakly closed nonunital star subalgebra containing a set. -/
noncomputable def ultraweakAdjoin (s : Set M) : NonUnitalStarSubalgebra ℂ M :=
  (NonUnitalStarAlgebra.adjoin ℂ s).ultraweakClosure (P := P)

theorem subset_ultraweakAdjoin (s : Set M) : s ⊆ ultraweakAdjoin (P := P) s :=
  (NonUnitalStarAlgebra.subset_adjoin ℂ s).trans (le_ultraweakClosure _)

instance (s : Set M) : IsUltraweakClosed (P := P) (ultraweakAdjoin (P := P) s) := by
  change IsUltraweakClosed (P := P)
    ((NonUnitalStarAlgebra.adjoin ℂ s).ultraweakClosure (P := P))
  infer_instance

theorem isUltraweakClosed_ultraweakAdjoin (s : Set M) :
    IsUltraweakClosed (P := P) (ultraweakAdjoin (P := P) s) :=
  inferInstance

theorem ultraweakAdjoin_le {s : Set M} {S : NonUnitalStarSubalgebra ℂ M}
    (hs : s ⊆ S) (hS : S.IsUltraweakClosed (P := P)) : ultraweakAdjoin (P := P) s ≤ S :=
  ultraweakClosure_minimal (NonUnitalStarAlgebra.adjoin_le hs) hS

end Closure

universe u v

section CStarAlgebra

variable {A : Type u} {Q : Type v} [CStarAlgebra A]
  [NormedAddCommGroup Q] [NormedSpace ℂ Q] [Predual ℂ A Q]

/-- The nonunital C-star algebra structure inherited by an ultraweakly closed nonunital star
subalgebra. -/
@[implicit_reducible]
noncomputable def IsUltraweakClosed.nonUnitalCStarAlgebra
    (S : NonUnitalStarSubalgebra ℂ A) (hS : S.IsUltraweakClosed (P := Q)) :
    NonUnitalCStarAlgebra S := by
  letI : IsClosed (S : Set A) := hS.norm_isClosed
  exact NonUnitalStarSubalgebra.nonUnitalCStarAlgebra S

end CStarAlgebra

section IsUnital

variable {A : Type u} {Q : Type v} [CStarAlgebra A]
  [NormedAddCommGroup Q] [NormedSpace ℂ Q] [Predual ℂ A Q]

/-- An ultraweakly closed nonunital star subalgebra of a dual C-star algebra has an internal
identity. -/
theorem IsUltraweakClosed.isUnital (S : NonUnitalStarSubalgebra ℂ A)
    (hS : S.IsUltraweakClosed (P := Q)) : IsUnital S := by
  letI : NonUnitalCStarAlgebra S := hS.nonUnitalCStarAlgebra S
  exact CStarAlgebra.isUnital_of_isClosed_submodule S.toSubmodule
    (toSubmoduleLinearIsometryEquiv S) hS.isClosed

/-- The ultraweak closure of a nonunital star subalgebra has an internal identity. -/
theorem isUnital_ultraweakClosure [CompleteSpace Q] [PartialOrder A] [StarOrderedRing A]
    (S : NonUnitalStarSubalgebra ℂ A) : IsUnital (S.ultraweakClosure (P := Q)) :=
  IsUltraweakClosed.isUnital (Q := Q) _
    (show IsUltraweakClosed (P := Q) (S.ultraweakClosure (P := Q)) from inferInstance)

end IsUnital

end NonUnitalStarSubalgebra

namespace IsStarProjection.Corner

variable {M P : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]
  {p : M} (hp : IsStarProjection p)

/-- The ambient nonunital star subalgebra representing a projection corner is ultraweakly
closed. -/
instance isUltraweakClosed_nonUnitalStarSubalgebra :
    NonUnitalStarSubalgebra.IsUltraweakClosed (P := P) (nonUnitalStarSubalgebra hp) where
  isClosed := by
    change IsClosed
      (Ultraweak.ofSubmodule (P := P) (rangeSubmodule hp) : Set σ(M, P))
    rw [← ultraweakRange_eq_ofSubmodule (P := P) hp]
    exact isClosed_ultraweakRange (P := P) hp

end IsStarProjection.Corner
