module

public import LeanOA.Mackey

@[expose] public section

/-!
# The Mackey topology associated to a continuous dual

This file defines `MackeySpace 𝕜 E`, the type synonym of `E` equipped with the Mackey
topology associated to the continuous dual of the existing topology on `E`. The explicit
equivalences `toMackeySpace` and `ofMackeySpace` are the public bridges across the synonym.
-/

noncomputable section

open scoped ComplexOrder

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E]

/-- A topological vector space equipped with the Mackey topology associated to its continuous
dual. -/
def MackeySpace (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] :=
  Mackey (weakDualPairing 𝕜 E).flip
deriving AddCommGroup, Module 𝕜, TopologicalSpace

variable (𝕜 E) in
/-- The canonical linear equivalence from `E` to `MackeySpace 𝕜 E`. -/
def toMackeySpace : E ≃ₗ[𝕜] MackeySpace 𝕜 E :=
  toMackey (weakDualPairing 𝕜 E).flip

variable (𝕜 E) in
/-- The canonical linear equivalence from `MackeySpace 𝕜 E` to `E`. -/
def ofMackeySpace : MackeySpace 𝕜 E ≃ₗ[𝕜] E :=
  (toMackeySpace 𝕜 E).symm

@[simp]
lemma ofMackeySpace_symm : (ofMackeySpace 𝕜 E).symm = toMackeySpace 𝕜 E := rfl

@[simp]
lemma toMackeySpace_symm : (toMackeySpace 𝕜 E).symm = ofMackeySpace 𝕜 E := rfl

@[simp]
lemma toMackeySpace_ofMackeySpace (x : MackeySpace 𝕜 E) :
    toMackeySpace 𝕜 E (ofMackeySpace 𝕜 E x) = x :=
  (toMackeySpace 𝕜 E).apply_symm_apply x

@[simp]
lemma ofMackeySpace_toMackeySpace (x : E) :
    ofMackeySpace 𝕜 E (toMackeySpace 𝕜 E x) = x :=
  (toMackeySpace 𝕜 E).symm_apply_apply x

variable (𝕜 E) in
/-- The explicit continuous linear equivalence between `MackeySpace 𝕜 E` and its underlying
pairing-level `Mackey` construction. -/
noncomputable def MackeySpace.mackeyCLE :
    MackeySpace 𝕜 E ≃L[𝕜] Mackey (weakDualPairing 𝕜 E).flip where
  toLinearEquiv := ofMackeySpace 𝕜 E ≪≫ₗ toMackey (weakDualPairing 𝕜 E).flip
  continuous_toFun := by
    unfold MackeySpace ofMackeySpace toMackeySpace
    exact continuous_id
  continuous_invFun := by
    unfold MackeySpace ofMackeySpace toMackeySpace
    exact continuous_id

@[simp]
lemma MackeySpace.mackeyCLE_apply (x : MackeySpace 𝕜 E) :
    mackeyCLE 𝕜 E x = toMackey (weakDualPairing 𝕜 E).flip (ofMackeySpace 𝕜 E x) :=
  rfl

@[simp]
lemma MackeySpace.mackeyCLE_symm_apply (x : Mackey (weakDualPairing 𝕜 E).flip) :
    (mackeyCLE 𝕜 E).symm x = toMackeySpace 𝕜 E (ofMackey x) :=
  rfl

instance : IsTopologicalAddGroup (MackeySpace 𝕜 E) :=
  (MackeySpace.mackeyCLE 𝕜 E).toHomeomorph.isInducing.topologicalAddGroup
    (MackeySpace.mackeyCLE 𝕜 E).toLinearMap

instance : ContinuousSMul 𝕜 (MackeySpace 𝕜 E) := by
  letI : ContinuousSMul 𝕜 (Mackey (weakDualPairing 𝕜 E).flip) :=
    PolarTopology.continuousSMul (B := (weakDualPairing 𝕜 E).flip)
      (𝔖 := {s | IsCompact s ∧ AbsConvex 𝕜 s}) fun _ hs ↦ by
      let _ := LinearMap.IsWeak.isTopologicalAddGroup (weakDualPairing 𝕜 E)
      let _ := LinearMap.IsWeak.continuousSMul (weakDualPairing 𝕜 E)
      exact hs.1.isVonNBounded 𝕜
  exact (MackeySpace.mackeyCLE 𝕜 E).toHomeomorph.isInducing.continuousSMul
    continuous_id rfl

instance : LocallyConvexSpace 𝕜 (MackeySpace 𝕜 E) :=
  (MackeySpace.mackeyCLE 𝕜 E).toHomeomorph.isInducing.locallyConvexSpace

end
