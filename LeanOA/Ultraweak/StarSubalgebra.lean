module

public import LeanOA.Ultraweak.Multiplication
public import LeanOA.Ultraweak.WStarAlgebra
public import Mathlib.Topology.Algebra.StarSubalgebra

@[expose] public section

/-!
# Ultraweakly closed star subalgebras

An ultraweakly closed subalgebra remains an ordinary `StarSubalgebra`; the proposition-valued
class `StarSubalgebra.IsUltraweakClosed` records compatibility with a specified predual.  This
keeps the algebraic carrier independent of the chosen analytic presentation.
-/

open Set
open scoped Ultraweak

namespace Ultraweak

variable {M P : Type*} [CStarAlgebra M]
  [NormedAddCommGroup P] [NormedSpace ℂ P] [Predual ℂ M P]

/-- A star subalgebra transported explicitly to the ultraweak copy of its ambient algebra. -/
noncomputable def ofStarSubalgebra (S : StarSubalgebra ℂ M) :
    StarSubalgebra ℂ σ(M, P) :=
  S.comap (starAlgEquiv M P).toStarAlgHom

@[simp]
lemma mem_ofStarSubalgebra (S : StarSubalgebra ℂ M) (x : σ(M, P)) :
    x ∈ ofStarSubalgebra (P := P) S ↔ ofUltraweak x ∈ S :=
  Iff.rfl

@[simp]
lemma ofStarSubalgebra_toSubmodule (S : StarSubalgebra ℂ M) :
    (ofStarSubalgebra (P := P) S).toSubmodule =
      ofSubmodule (P := P) S.toSubmodule := by
  ext
  simp

end Ultraweak

namespace StarSubalgebra

variable {M P : Type*} [CStarAlgebra M]
  [NormedAddCommGroup P] [NormedSpace ℂ P] [Predual ℂ M P]

/-- Compatibility class asserting that a star subalgebra is closed in the ultraweak topology
specified by `P`. -/
class IsUltraweakClosed (S : StarSubalgebra ℂ M) : Prop where
  isClosed :
    IsClosed (Ultraweak.ofSubmodule (P := P) S.toSubmodule : Set σ(M, P))

namespace IsUltraweakClosed

variable {S : StarSubalgebra ℂ M}

/-- An ultraweakly closed star subalgebra is norm closed. -/
theorem norm_isClosed (hS : S.IsUltraweakClosed (P := P)) : IsClosed (S : Set M) := by
  convert hS.isClosed.preimage (continuous_toUltraweak (M := M) (P := P)) using 1
  ext x
  simp

end IsUltraweakClosed

section Closure

variable [PartialOrder M] [StarOrderedRing M] [CompleteSpace P]

/-- The ultraweak closure of a star subalgebra, retained as an ordinary star subalgebra of `M`. -/
noncomputable def ultraweakClosure (S : StarSubalgebra ℂ M) : StarSubalgebra ℂ M :=
  (Ultraweak.ofStarSubalgebra (P := P) S).topologicalClosure.comap
    (Ultraweak.starAlgEquiv M P).symm.toStarAlgHom

@[simp]
lemma mem_ultraweakClosure (S : StarSubalgebra ℂ M) (x : M) :
    x ∈ S.ultraweakClosure (P := P) ↔
      toUltraweak ℂ P x ∈
        closure (Ultraweak.ofStarSubalgebra (P := P) S : Set σ(M, P)) :=
  Iff.rfl

theorem le_ultraweakClosure (S : StarSubalgebra ℂ M) : S ≤ S.ultraweakClosure (P := P) :=
  fun x hx ↦ by
    rw [mem_ultraweakClosure]
    exact subset_closure <| by
      change ofUltraweak (toUltraweak ℂ P x) ∈ S
      simpa using hx

instance (S : StarSubalgebra ℂ M) :
    IsUltraweakClosed (P := P) (S.ultraweakClosure (P := P)) where
  isClosed := by
    rw [← Ultraweak.ofStarSubalgebra_toSubmodule]
    convert StarSubalgebra.isClosed_topologicalClosure
      (Ultraweak.ofStarSubalgebra (P := P) S) using 1
    ext x
    simp [mem_ultraweakClosure]

theorem isUltraweakClosed_ultraweakClosure (S : StarSubalgebra ℂ M) :
    IsUltraweakClosed (P := P) (S.ultraweakClosure (P := P)) :=
  inferInstance

theorem ultraweakClosure_minimal {S T : StarSubalgebra ℂ M}
    (hST : S ≤ T) (hT : T.IsUltraweakClosed (P := P)) : S.ultraweakClosure (P := P) ≤ T := by
  intro x hx
  rw [mem_ultraweakClosure] at hx
  have : toUltraweak ℂ P x ∈ Ultraweak.ofStarSubalgebra (P := P) T :=
    closure_minimal (fun y hy ↦ by simpa using hST <| by simpa using hy) hT.isClosed hx
  simpa using this

@[simp]
theorem ultraweakClosure_eq_self {S : StarSubalgebra ℂ M} [S.IsUltraweakClosed (P := P)] :
    S.ultraweakClosure (P := P) = S :=
  le_antisymm (ultraweakClosure_minimal le_rfl inferInstance) (le_ultraweakClosure S)

/-- Ultraweak closure preserves commutativity. -/
instance (S : StarSubalgebra ℂ M) [hS : IsMulCommutative S] :
    IsMulCommutative (S.ultraweakClosure (P := P)) := by
  let T := Ultraweak.ofStarSubalgebra (P := P) S
  have hT : IsMulCommutative T := .of_setLike_mul_comm fun x hx y hy ↦ by
    rw [← ofUltraweak_inj, Ultraweak.ofUltraweak_mul, Ultraweak.ofUltraweak_mul]
    exact setLike_mul_comm
      (Ultraweak.mem_ofStarSubalgebra (P := P) S x |>.mp hx)
      (Ultraweak.mem_ofStarSubalgebra (P := P) S y |>.mp hy)
  letI : CommRing T.topologicalClosure :=
    StarSubalgebra.commRingTopologicalClosure T hT.is_comm.comm
  refine .of_setLike_mul_comm fun x hx y hy ↦ ?_
  let x' : T.topologicalClosure := ⟨toUltraweak ℂ P x, hx⟩
  let y' : T.topologicalClosure := ⟨toUltraweak ℂ P y, hy⟩
  apply (toUltraweak_inj (𝕜 := ℂ) (P := P)).mp
  rw [Ultraweak.toUltraweak_mul, Ultraweak.toUltraweak_mul]
  exact congr_arg Subtype.val (mul_comm x' y')

/-- The smallest ultraweakly closed star subalgebra containing a set. -/
noncomputable def ultraweakAdjoin (s : Set M) : StarSubalgebra ℂ M :=
  (StarAlgebra.adjoin ℂ s).ultraweakClosure (P := P)

theorem subset_ultraweakAdjoin (s : Set M) : s ⊆ ultraweakAdjoin (P := P) s :=
  (StarAlgebra.subset_adjoin ℂ s).trans (le_ultraweakClosure _)

instance (s : Set M) : IsUltraweakClosed (P := P) (ultraweakAdjoin (P := P) s) := by
  change IsUltraweakClosed (P := P)
    ((StarAlgebra.adjoin ℂ s).ultraweakClosure (P := P))
  infer_instance

theorem isUltraweakClosed_ultraweakAdjoin (s : Set M) :
    IsUltraweakClosed (P := P) (ultraweakAdjoin (P := P) s) :=
  inferInstance

theorem ultraweakAdjoin_le {s : Set M} {S : StarSubalgebra ℂ M}
    (hs : s ⊆ S) (hS : S.IsUltraweakClosed (P := P)) : ultraweakAdjoin (P := P) s ≤ S :=
  ultraweakClosure_minimal (StarAlgebra.adjoin_le hs) hS

/-- A masa is ultraweakly closed. -/
theorem IsMasa.isUltraweakClosed (S : StarSubalgebra ℂ M) [hS : S.IsMasa] :
    S.IsUltraweakClosed (P := P) := by
  have hEq : S.ultraweakClosure (P := P) = S := le_antisymm
    (hS.maximal (S.ultraweakClosure (P := P)) <| le_ultraweakClosure (P := P) S)
    (le_ultraweakClosure (P := P) S)
  rw [← hEq]
  infer_instance

end Closure

universe u v

section CStarAlgebra

variable {A : Type u} {Q : Type v} [CStarAlgebra A]
  [NormedAddCommGroup Q] [NormedSpace ℂ Q] [Predual ℂ A Q]

/-- The C-star algebra structure inherited by an ultraweakly closed star subalgebra. -/
@[implicit_reducible]
noncomputable def IsUltraweakClosed.cstarAlgebra (S : StarSubalgebra ℂ A)
    (hS : S.IsUltraweakClosed (P := Q)) : CStarAlgebra S := by
  letI : IsClosed (S : Set A) := hS.norm_isClosed
  exact StarSubalgebra.cstarAlgebra S

end CStarAlgebra

section WStarAlgebra

variable {A Q : Type u} [CStarAlgebra A]
  [NormedAddCommGroup Q] [NormedSpace ℂ Q] [CompleteSpace Q] [Predual ℂ A Q]

/-- The explicit linear isometry between a star subalgebra and the ambient submodule with the same
carrier. -/
private noncomputable def toSubmoduleLinearIsometryEquiv (S : StarSubalgebra ℂ A) :
    S ≃ₗᵢ[ℂ] S.toSubmodule where
  toFun x := ⟨x, x.property⟩
  invFun x := ⟨x, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

/-- An ultraweakly closed star subalgebra, equipped with its explicitly induced C-star structure,
is a W-star algebra. -/
theorem IsUltraweakClosed.wStarAlgebra (S : StarSubalgebra ℂ A)
    (hS : S.IsUltraweakClosed (P := Q)) : @WStarAlgebra S (hS.cstarAlgebra S) := by
  letI : CStarAlgebra S := hS.cstarAlgebra S
  exact WStarAlgebra.of_isClosed_submodule S Q A S.toSubmodule
    (toSubmoduleLinearIsometryEquiv S) hS.isClosed

end WStarAlgebra

end StarSubalgebra
