module

public import Mathlib.Analysis.LocallyConvex.WeakOperatorTopology
public import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM

/-!
# Pointwise convergence and the weak operator topology

This file supplies the canonical continuous identity map from continuous linear maps with the
topology of pointwise convergence to continuous linear maps with the weak operator topology.
-/

@[expose] public section

variable {𝕜 E F : Type*} [NormedField 𝕜]
  [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
  [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F] [Module 𝕜 F]
  [ContinuousConstSMul 𝕜 F]

namespace PointwiseConvergenceCLM

/-- The canonical continuous identity map from the topology of pointwise convergence to the weak
operator topology. -/
def toWOT : (E →Lₚₜ[𝕜] F) →L[𝕜] (E →WOT[𝕜] F) where
  toFun A := ContinuousLinearMapWOT.ofCLM A
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := ContinuousLinearMapWOT.continuous_of_dual_apply_continuous fun x y ↦
    y.cont.comp (continuous_eval_const x)

@[simp]
lemma toWOT_apply (A : E →Lₚₜ[𝕜] F) (x : E) : toWOT A x = A x := rfl

/-- A weak-operator closed set of continuous linear maps is closed for the topology of pointwise
convergence on the same underlying set. -/
theorem isClosed_pointwise_of_isClosed_wot (S : Set (E →L[𝕜] F))
    (hS : IsClosed {A : E →WOT[𝕜] F | A.toCLM ∈ S}) :
    IsClosed {A : E →Lₚₜ[𝕜] F | (A : E →L[𝕜] F) ∈ S} := by
  change IsClosed (toWOT ⁻¹' {A : E →WOT[𝕜] F | A.toCLM ∈ S})
  exact hS.preimage toWOT.continuous

end PointwiseConvergenceCLM
