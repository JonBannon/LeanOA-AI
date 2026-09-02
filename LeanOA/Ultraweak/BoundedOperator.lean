module

public import LeanOA.Mathlib.Analysis.InnerProductSpace.OperatorPredual
public import LeanOA.Ultraweak.Basic

/-!
# The concrete specified predual of bounded operators

This file installs the norm closure of the vector-functional span as Sak-AI's specified `Predual`
for continuous linear maps into a Hilbert space.  The mathematical construction and its general
isometric duality theorem live in the upstream-shaped `OperatorPredual` module; this file is only
the operator-algebra-facing assembly layer.
-/

@[expose] public section

open scoped InnerProduct InnerProductSpace

noncomputable section

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

set_option maxSynthPendingDepth 4

/-- The norm-closed vector-functional space, exposed through a short carrier name for use as a
specified predual.  This wrapper is canonically isometric to the closure constructed in
`OperatorPredual`; its purpose is to keep downstream typeclass synthesis within the project-wide
depth bound. -/
def VectorFunctionalPredual (𝕜 E F : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] : Type _ :=
  vectorFunctionalClosure (𝕜 := 𝕜) (E := E) (F := F)

instance instNormedAddCommGroupVectorFunctionalPredual :
    NormedAddCommGroup (VectorFunctionalPredual 𝕜 E F) :=
  inferInstanceAs (NormedAddCommGroup
    (vectorFunctionalClosure (𝕜 := 𝕜) (E := E) (F := F)))

instance instSMulVectorFunctionalPredual :
    SMul 𝕜 (VectorFunctionalPredual 𝕜 E F) :=
  inferInstanceAs (SMul 𝕜
    (vectorFunctionalClosure (𝕜 := 𝕜) (E := E) (F := F)))

instance instModuleVectorFunctionalPredual :
    Module 𝕜 (VectorFunctionalPredual 𝕜 E F) :=
  inferInstanceAs (Module 𝕜
    (vectorFunctionalClosure (𝕜 := 𝕜) (E := E) (F := F)))

instance instNormedSpaceVectorFunctionalPredual :
    NormedSpace 𝕜 (VectorFunctionalPredual 𝕜 E F) :=
  inferInstanceAs (NormedSpace 𝕜
    (vectorFunctionalClosure (𝕜 := 𝕜) (E := E) (F := F)))

instance instCompleteSpaceVectorFunctionalPredual :
    CompleteSpace (VectorFunctionalPredual 𝕜 E F) :=
  inferInstanceAs (CompleteSpace
    (vectorFunctionalClosure (𝕜 := 𝕜) (E := E) (F := F)))

/-- The short predual carrier is canonically the norm-closed vector-functional submodule. -/
def vectorFunctionalPredualEquivClosure :
    VectorFunctionalPredual 𝕜 E F ≃ₗᵢ[𝕜]
      vectorFunctionalClosure (𝕜 := 𝕜) (E := E) (F := F) :=
  LinearIsometryEquiv.refl 𝕜 _

omit [CompleteSpace F] in
/-- A vector functional, regarded as an element of the short concrete-predual carrier. -/
def vectorFunctionalInPredual (xi : E) (eta : F) :
    VectorFunctionalPredual 𝕜 E F :=
  (vectorFunctionalPredualEquivClosure
    (𝕜 := 𝕜) (E := E) (F := F)).symm (vectorFunctionalInClosure xi eta)

omit [CompleteSpace F] in
@[simp]
lemma vectorFunctionalPredualEquivClosure_vectorFunctionalInPredual (xi : E) (eta : F) :
    vectorFunctionalPredualEquivClosure
        (vectorFunctionalInPredual (𝕜 := 𝕜) xi eta) =
      vectorFunctionalInClosure xi eta :=
  rfl

omit [CompleteSpace F] in
@[simp]
lemma norm_vectorFunctionalInPredual (xi : E) (eta : F) :
    ‖vectorFunctionalInPredual (𝕜 := 𝕜) xi eta‖ = ‖xi‖ * ‖eta‖ := by
  change ‖(vectorFunctionalPredualEquivClosure
    (𝕜 := 𝕜) (E := E) (F := F)).symm (vectorFunctionalInClosure xi eta)‖ = _
  rw [(vectorFunctionalPredualEquivClosure
    (𝕜 := 𝕜) (E := E) (F := F)).symm.norm_map,
    norm_vectorFunctionalInClosure]

/-! ## The dense finite-coefficient core -/

/-- The canonical isometric inclusion of the finite vector-functional span into the short
predual carrier. -/
def vectorFunctionalSpanToPredualₗᵢ :
    vectorFunctionalSpan (𝕜 := 𝕜) (E := E) (F := F) →ₗᵢ[𝕜]
      VectorFunctionalPredual 𝕜 E F :=
  (vectorFunctionalPredualEquivClosure
    (𝕜 := 𝕜) (E := E) (F := F)).symm.toLinearIsometry.comp
      (vectorFunctionalSpanToClosureₗᵢ (𝕜 := 𝕜) (E := E) (F := F))

/-- The continuous-linear inclusion of the finite vector-functional span into the short predual
carrier. -/
def vectorFunctionalSpanToPredual :
    vectorFunctionalSpan (𝕜 := 𝕜) (E := E) (F := F) →L[𝕜]
      VectorFunctionalPredual 𝕜 E F :=
  vectorFunctionalSpanToPredualₗᵢ.toContinuousLinearMap

omit [CompleteSpace F] in
@[simp]
lemma vectorFunctionalSpanToPredual_vectorFunctional (xi : E) (eta : F) :
    vectorFunctionalSpanToPredual
        (⟨vectorFunctional (𝕜 := 𝕜) xi eta,
          vectorFunctional_mem_span xi eta⟩ :
          vectorFunctionalSpan (𝕜 := 𝕜) (E := E) (F := F)) =
      vectorFunctionalInPredual xi eta :=
  rfl

omit [CompleteSpace F] in
@[simp]
lemma vectorFunctionalPredualEquivClosure_spanToPredual
    (f : vectorFunctionalSpan (𝕜 := 𝕜) (E := E) (F := F)) :
    vectorFunctionalPredualEquivClosure (vectorFunctionalSpanToPredual f) =
      vectorFunctionalSpanToClosure f :=
  rfl

omit [CompleteSpace F] in
@[simp]
lemma coe_vectorFunctionalSpanToPredual
    (f : vectorFunctionalSpan (𝕜 := 𝕜) (E := E) (F := F)) :
    (vectorFunctionalPredualEquivClosure (vectorFunctionalSpanToPredual f) :
      (E →L[𝕜] F) →L[𝕜] 𝕜) = f := by
  rw [vectorFunctionalPredualEquivClosure_spanToPredual,
    vectorFunctionalSpanToClosure_apply]

omit [CompleteSpace F] in
/-- The finite vector-functional span has dense image in the short predual carrier. -/
theorem denseRange_vectorFunctionalSpanToPredual :
    DenseRange (vectorFunctionalSpanToPredual
      (𝕜 := 𝕜) (E := E) (F := F)) := by
  let e := vectorFunctionalPredualEquivClosure (𝕜 := 𝕜) (E := E) (F := F)
  have he : DenseRange e.symm := e.symm.surjective.denseRange
  have hi := denseRange_vectorFunctionalSpanToClosure (𝕜 := 𝕜) (E := E) (F := F)
  have hcomp := he.comp hi e.symm.continuous
  change DenseRange (fun f ↦ e.symm (vectorFunctionalSpanToClosure f))
  exact hcomp

/-- The copy of the finite vector-functional span inside the short predual carrier. -/
def vectorFunctionalPredualSpan : Submodule 𝕜 (VectorFunctionalPredual 𝕜 E F) :=
  LinearMap.range (vectorFunctionalSpanToPredual
    (𝕜 := 𝕜) (E := E) (F := F)).toLinearMap

omit [CompleteSpace F] in
/-- The finite coefficient core is norm dense in the short predual carrier. -/
theorem dense_vectorFunctionalPredualSpan :
    Dense (vectorFunctionalPredualSpan (𝕜 := 𝕜) (E := E) (F := F) :
      Set (VectorFunctionalPredual 𝕜 E F)) := by
  change DenseRange (vectorFunctionalSpanToPredual (𝕜 := 𝕜) (E := E) (F := F))
  exact denseRange_vectorFunctionalSpanToPredual

/-- Bounded maps into a complete Hilbert space are canonically the dual of the short
vector-functional predual carrier. -/
def vectorFunctionalPredualEquivDual :
    (E →L[𝕜] F) ≃ₗᵢ[𝕜] StrongDual 𝕜 (VectorFunctionalPredual 𝕜 E F) :=
  vectorFunctionalClosureEquivDual

/-- The norm-closed vector-functional space is a specified predual of the bounded maps into a
Hilbert space.  In particular this supplies the concrete predual of `B(H)`. -/
noncomputable instance instPredualVectorFunctionalPredual :
    Predual 𝕜 (E →L[𝕜] F) (VectorFunctionalPredual 𝕜 E F) where
  equivDual := vectorFunctionalPredualEquivDual

@[simp]
lemma vectorFunctionalPredual_predualEquivDual_apply_apply (T : E →L[𝕜] F)
    (f : VectorFunctionalPredual 𝕜 E F) :
    Predual.equivDual (𝕜 := 𝕜)
      (M := E →L[𝕜] F)
      (P := VectorFunctionalPredual 𝕜 E F) T f =
        (vectorFunctionalPredualEquivClosure f).1 T :=
  rfl

@[simp]
lemma vectorFunctionalPredualEvaluation_vectorFunctionalInPredual
    (T : E →L[𝕜] F) (xi : E) (eta : F) :
    Predual.equivDual (𝕜 := 𝕜)
      (M := E →L[𝕜] F) (P := VectorFunctionalPredual 𝕜 E F) T
      (vectorFunctionalInPredual xi eta) = ⟪eta, T xi⟫_𝕜 := by
  rw [vectorFunctionalPredual_predualEquivDual_apply_apply,
    vectorFunctionalPredualEquivClosure_vectorFunctionalInPredual]
  rfl

end ContinuousLinearMap
