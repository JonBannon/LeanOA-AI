module

public import Mathlib.Topology.Algebra.Module.Spaces.WeakBilin
public import Mathlib.Topology.Algebra.Module.Equiv

@[expose] public section

variable {𝕜 E F E' F' : Type*}
  [CommSemiring 𝕜]
  [AddCommMonoid E] [Module 𝕜 E] [AddCommMonoid F] [Module 𝕜 F]
  [AddCommMonoid E'] [Module 𝕜 E'] [AddCommMonoid F'] [Module 𝕜 F']
  (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

namespace WeakBilin

/-- The canonical linear equivalence (over `𝕝`) between `WeakBilin (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)`
and `E`. -/
noncomputable def linearEquiv (𝕝 : Type*) [CommSemiring 𝕝] [Module 𝕝 E] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) :
    WeakBilin B ≃ₗ[𝕝] E :=
  LinearEquiv.refl ..

@[simp]
lemma linearEquiv_apply (𝕝 : Type*) [CommSemiring 𝕝] [Module 𝕝 E]
    (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) (x : WeakBilin B) : linearEquiv 𝕝 B x = x :=
  rfl

@[simp]
lemma linearEquiv_symm_apply (𝕝 : Type*) [CommSemiring 𝕝] [Module 𝕝 E]
    (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) (x : E) : (linearEquiv 𝕝 B).symm x = x :=
  rfl

/-- The dual pairing between `WeakBilin (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)` and `F`. In order to avoid abuse
of the definitional equality between `E` and `WeakBilin B`, it is necessary to use this pairing
instead of `B` itself when considering statements involving the weak topology induced by the
pairing, such as the bipolar theorem. -/
noncomputable def pairing : WeakBilin B →ₗ[𝕜] F →ₗ[𝕜] 𝕜 :=
  (linearEquiv 𝕜 B).symm.arrowCongr (.refl _ _) B

variable {B} in
lemma pairing_apply (x : WeakBilin B) :
    pairing B x = B (linearEquiv 𝕜 B x) :=
  rfl

variable [TopologicalSpace 𝕜]

/-- The coercion `(fun x y => B x y) : E → (F → 𝕜)` is continuous. -/
theorem coeFn_continuous' : Continuous fun (x : WeakBilin B) y => pairing B x y :=
  continuous_induced_dom

@[fun_prop]
theorem eval_continuous' (y : F) : Continuous fun x : WeakBilin B => pairing B x y :=
  (continuous_pi_iff.mp (coeFn_continuous B)) y

theorem continuous_of_continuous_eval' {α : Type*} [TopologicalSpace α] {g : α → WeakBilin B}
    (h : ∀ y, Continuous fun a => pairing B (g a) y) : Continuous g :=
  continuous_induced_rng.2 (continuous_pi_iff.mpr h)

/-- Restricting the right test space of a bilinear pairing gives a canonical continuous linear
identity from the original weak topology to the weak topology induced by the smaller family of
tests. -/
noncomputable def restrictRightL (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) (i : F' →ₗ[𝕜] F) :
    WeakBilin B →L[𝕜] WeakBilin ((B.flip.comp i).flip) where
  toLinearMap :=
    (linearEquiv 𝕜 ((B.flip.comp i).flip)).symm.toLinearMap.comp
      (linearEquiv 𝕜 B).toLinearMap
  cont := by
    apply continuous_of_continuous_eval
    intro y
    convert eval_continuous B (i y) using 1
    funext x
    rfl

lemma linearEquiv_restrictRightL (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) (i : F' →ₗ[𝕜] F)
    (x : WeakBilin B) :
    linearEquiv 𝕜 ((B.flip.comp i).flip) (restrictRightL B i x) =
      linearEquiv 𝕜 B x :=
  rfl

/-- Restricting the right test space evaluates by applying the original pairing to the included
test vector. -/
@[simp]
lemma pairing_restrictRightL (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) (i : F' →ₗ[𝕜] F)
    (x : WeakBilin B) (y : F') :
    pairing ((B.flip.comp i).flip) (restrictRightL B i x) y = pairing B x (i y) :=
  rfl

lemma isInducing (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) :
    Topology.IsInducing (fun x i ↦ pairing B x i) where
  eq_induced := rfl

/-- Weak topologies induced by equivalent bilinear forms are continuously linearly equivalent. -/
@[simps!]
protected noncomputable def congr (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) (e : E ≃ₗ[𝕜] E') (f : F ≃ₗ[𝕜] F')
    (B' : E' →ₗ[𝕜] F' →ₗ[𝕜] 𝕜) (hB : e.arrowCongr (f.arrowCongr (.refl ..)) B = B') :
    WeakBilin B ≃L[𝕜] WeakBilin B' where
  toLinearEquiv :=
    { toFun := e
      invFun := e.symm
      left_inv := e.symm_apply_apply
      right_inv := e.apply_symm_apply
      map_add' := e.map_add
      map_smul' := e.map_smul }
  continuous_toFun := by
    apply continuous_of_continuous_eval B' fun y' ↦ ?_
    simpa [← hB] using WeakBilin.eval_continuous B (f.symm y')
  continuous_invFun := by
    apply continuous_of_continuous_eval B fun y ↦ ?_
    simpa [← hB] using WeakBilin.eval_continuous B' (f y)

end WeakBilin
