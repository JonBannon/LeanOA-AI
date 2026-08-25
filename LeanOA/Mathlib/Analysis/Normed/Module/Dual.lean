module

public import Mathlib.Analysis.LocallyConvex.Polar
public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-!
# Continuous duals of quotient spaces

This file upgrades the algebraic equivalence between the dual of a quotient and the annihilator
of the subspace to a linear isometric equivalence of continuous duals.
-/

@[expose] public section

open ContinuousLinearMap

namespace Submodule

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The continuous linear map induced on a quotient has operator norm at most that of the
original map. -/
theorem norm_liftQL_le (S : Submodule 𝕜 E) [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    (f : E →L[𝕜] F) (hf : S ≤ f.ker) : ‖S.liftQL f hf‖ ≤ ‖f‖ := by
  let f' := f.toLinearMap.toAddMonoidHom.mkNormedAddGroupHom ‖f‖ f.le_opNorm
  have hf' : ∀ x ∈ S.toAddSubgroup, f' x = 0 := fun x hx ↦ hf hx
  refine (S.liftQL f hf).opNorm_le_bound (norm_nonneg f) fun x ↦ ?_
  exact (QuotientAddGroup.norm_lift_apply_le f' hf' x).trans <|
    mul_le_mul_of_nonneg_right
      (AddMonoidHom.mkNormedAddGroupHom_norm_le _ (norm_nonneg f) f.le_opNorm) (norm_nonneg x)

variable (S : Submodule 𝕜 E)

/-- Precomposition with the quotient map, viewed as a map into the annihilator of the
submodule. -/
def dualQuotientToAnnihilatorₗ :
    StrongDual 𝕜 (E ⧸ S) →ₗ[𝕜] StrongDual.polarSubmodule 𝕜 S where
  toFun f := ⟨f ∘L S.mkQL, by
    rw [StrongDual.mem_polarSubmodule]
    intro x hx
    rw [comp_apply, S.mkQL_apply, S.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero S).mpr hx, map_zero]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
lemma dualQuotientToAnnihilatorₗ_apply_apply (f : StrongDual 𝕜 (E ⧸ S)) (x : E) :
    (dualQuotientToAnnihilatorₗ S f).1 x = f (Submodule.Quotient.mk x) :=
  by simp [dualQuotientToAnnihilatorₗ, S.mkQ_apply]

lemma norm_dualQuotientToAnnihilatorₗ (f : StrongDual 𝕜 (E ⧸ S)) :
    ‖dualQuotientToAnnihilatorₗ S f‖ = ‖f‖ := by
  apply le_antisymm
  · exact (f ∘L S.mkQL).opNorm_le_bound (norm_nonneg f) fun x ↦
      (f.le_opNorm _).trans <| mul_le_mul_of_nonneg_left
        (Submodule.Quotient.norm_mk_le S x) (norm_nonneg f)
  · let g : StrongDual 𝕜 E := f ∘L S.mkQL
    have hg : S ≤ g.ker := by
      intro x hx
      change f (Submodule.Quotient.mk x) = 0
      rw [(Submodule.Quotient.mk_eq_zero S).mpr hx, map_zero]
    rw [← show S.liftQL g hg = f by
      ext x
      induction x using Quotient.inductionOn
      rw [S.liftQL_apply]
      change S.liftQ g.toLinearMap hg (Quotient.mk _) = _
      rw [S.liftQ_apply]
      exact dualQuotientToAnnihilatorₗ_apply_apply S f _]
    exact norm_liftQL_le S g hg

/-- Precomposition with the quotient map bijects the continuous dual of the quotient with the
annihilator. -/
lemma dualQuotientToAnnihilatorₗ_bijective :
    Function.Bijective (dualQuotientToAnnihilatorₗ S) := by
  constructor
  · intro f g h
    ext x
    induction x using Quotient.inductionOn
    exact congrArg (fun k : StrongDual.polarSubmodule 𝕜 S ↦ k.1 _) h
  · intro g
    refine ⟨S.liftQL g.1 (fun x hx ↦ LinearMap.mem_ker.mpr <|
      StrongDual.mem_polarSubmodule 𝕜 S g |>.mp g.property x hx), ?_⟩
    apply Subtype.ext
    ext x
    rfl

/-- The continuous dual of a quotient is linearly isometric to the annihilator of the
submodule. -/
noncomputable def dualQuotientEquivAnnihilator :
    StrongDual 𝕜 (E ⧸ S) ≃ₗᵢ[𝕜] StrongDual.polarSubmodule 𝕜 S where
  toLinearEquiv := LinearEquiv.ofBijective (dualQuotientToAnnihilatorₗ S)
    (dualQuotientToAnnihilatorₗ_bijective S)
  norm_map' := norm_dualQuotientToAnnihilatorₗ S

@[simp]
lemma dualQuotientEquivAnnihilator_apply_apply (f : StrongDual 𝕜 (E ⧸ S)) (x : E) :
    (dualQuotientEquivAnnihilator S f).1 x = f (Submodule.Quotient.mk x) :=
  by simp [dualQuotientEquivAnnihilator]

end Submodule
