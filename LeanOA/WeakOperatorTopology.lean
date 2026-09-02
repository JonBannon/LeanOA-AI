module

public import LeanOA.IsWeak
public import LeanOA.Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology

/-!
# The vector-functional dual pair for the weak operator topology

This file connects Mathlib's weak operator topology to Sak-AI's proposition-valued
`LinearMap.IsWeak` interface. The test vectors are the algebraic span of the vector functionals;
no norm completion or concrete predual is asserted here.
-/

@[expose] public section

namespace ContinuousLinearMapWOT

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Evaluation of a weak-operator-topology map against the span of the vector functionals. -/
noncomputable def vectorFunctionalPairing :
    (E →WOT[𝕜] F) →ₗ[𝕜]
      ContinuousLinearMap.vectorFunctionalSpan
        (𝕜 := 𝕜) (E := E) (F := F) →ₗ[𝕜] 𝕜 :=
  (ContinuousLinearMap.vectorFunctionalPairing
    (𝕜 := 𝕜) (E := E) (F := F)).comp
      (ContinuousLinearMapWOT.linearEquiv 𝕜).toLinearMap

@[simp]
lemma vectorFunctionalPairing_apply (T : E →WOT[𝕜] F)
    (f : ContinuousLinearMap.vectorFunctionalSpan
      (𝕜 := 𝕜) (E := E) (F := F)) :
    vectorFunctionalPairing T f = f.1 T.toCLM :=
  rfl

/-- The vector-functional pairing separates weak-operator-topology maps. -/
theorem vectorFunctionalPairing_separatingLeft :
    (vectorFunctionalPairing (𝕜 := 𝕜) (E := E) (F := F)).SeparatingLeft := by
  intro T hT
  apply toCLM_injective
  rw [toCLM_zero]
  apply ContinuousLinearMap.eq_zero_of_forall_mem_vectorFunctionalSpan_eq_zero
  intro f hf
  simpa using hT ⟨f, hf⟩

/-- Evaluation against weak-operator-topology maps separates the vector-functional span. -/
theorem vectorFunctionalPairing_separatingRight :
    (vectorFunctionalPairing (𝕜 := 𝕜) (E := E) (F := F)).SeparatingRight := by
  intro f hf
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro T
  simpa using hf (ofCLM T)

section Complete

variable [CompleteSpace F]

/-- Mathlib's weak operator topology is exactly the weak topology induced by the span of the
vector functionals. -/
noncomputable instance vectorFunctionalPairing_isWeak :
    (vectorFunctionalPairing (𝕜 := 𝕜) (E := E) (F := F)).IsWeak :=
  LinearMap.IsWeak.congr
    (WeakBilin.pairing (ContinuousLinearMap.vectorFunctionalPairing
      (𝕜 := 𝕜) (E := E) (F := F)))
    (vectorFunctionalPairing (𝕜 := 𝕜) (E := E) (F := F))
    (vectorFunctionalWeakEquiv (𝕜 := 𝕜) (E := E) (F := F))
    (.refl _ _) (by ext; rfl)

/-- The span of the vector functionals is linearly equivalent to the full continuous dual of the
weak operator topology. This is the weak representation theorem; it is not an identification with
the norm-completed predual of `B(H)`. -/
noncomputable def vectorFunctionalSpanEquivDual :
    ContinuousLinearMap.vectorFunctionalSpan
        (𝕜 := 𝕜) (E := E) (F := F) ≃ₗ[𝕜]
      StrongDual 𝕜 (E →WOT[𝕜] F) :=
  LinearMap.IsWeak.rightDualEquiv
    (𝕜 := 𝕜) (E := E →WOT[𝕜] F)
    (F := ContinuousLinearMap.vectorFunctionalSpan
      (𝕜 := 𝕜) (E := E) (F := F))
    (vectorFunctionalPairing (𝕜 := 𝕜) (E := E) (F := F))
    (vectorFunctionalPairing_separatingRight (𝕜 := 𝕜) (E := E) (F := F))

@[simp]
lemma vectorFunctionalSpanEquivDual_apply_apply
    (f : ContinuousLinearMap.vectorFunctionalSpan
      (𝕜 := 𝕜) (E := E) (F := F)) (T : E →WOT[𝕜] F) :
    vectorFunctionalSpanEquivDual f T = f.1 T.toCLM :=
  rfl

end Complete

end ContinuousLinearMapWOT
