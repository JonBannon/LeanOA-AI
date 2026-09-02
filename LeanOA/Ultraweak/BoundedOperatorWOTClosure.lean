module

public import LeanOA.Ultraweak.BoundedOperator
public import LeanOA.Ultraweak.TestWeak
public import LeanOA.WeakOperatorTopology
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Topology.Algebra.NonUnitalStarAlgebra

/-!
# WOT closure for bounded-operator star subalgebras

This file transports the closure of a nonunital star subalgebra through Mathlib's existing weak
operator topology carrier.  It also identifies that closure with the test-weak closure induced by
the finite vector-functional core inside the concrete predual of `B(H)`.

The finite coefficient core used here is distinct from Sakai's space of countable coefficient
series.  In particular, this file introduces no alternative WOT or `σ`-WOT topology and asserts
no representation theorem for the full concrete predual.
-/

@[expose] public section

open Set
open scoped InnerProductSpace Ultraweak

noncomputable section

namespace ContinuousLinearMapWOT

variable {𝕜 H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- The canonical star-algebra equivalence from Mathlib's WOT carrier to bounded operators. -/
def starAlgEquiv : (H →WOT[𝕜] H) ≃⋆ₐ[𝕜] (H →L[𝕜] H) :=
  { ContinuousLinearMapWOT.linearEquiv 𝕜,
      ContinuousLinearMapWOT.ringEquiv with
    map_star' := fun _ ↦ rfl }

@[simp]
lemma starAlgEquiv_apply (T : H →WOT[𝕜] H) :
    starAlgEquiv T = T.toCLM :=
  rfl

@[simp]
lemma starAlgEquiv_symm_apply (T : H →L[𝕜] H) :
    starAlgEquiv.symm T = ContinuousLinearMapWOT.ofCLM T :=
  rfl

end ContinuousLinearMapWOT

namespace NonUnitalStarSubalgebra

variable {𝕜 H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- The WOT closure of a nonunital star subalgebra, transported back to bounded operators. -/
def wotClosure (S : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) :
    NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H) :=
  ((S.comap
      (ContinuousLinearMapWOT.starAlgEquiv (𝕜 := 𝕜) (H := H)).toNonUnitalStarAlgHom
    ).topologicalClosure).comap
      (ContinuousLinearMapWOT.starAlgEquiv (𝕜 := 𝕜) (H := H)).symm.toNonUnitalStarAlgHom

@[simp]
lemma mem_wotClosure (S : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H))
    (T : H →L[𝕜] H) :
    T ∈ S.wotClosure ↔
      ContinuousLinearMapWOT.ofCLM T ∈
        closure {A : H →WOT[𝕜] H | A.toCLM ∈ S} :=
  Iff.rfl

theorem le_wotClosure (S : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) :
    S ≤ S.wotClosure := by
  intro T hT
  rw [mem_wotClosure]
  exact subset_closure hT

theorem isClosed_wotClosure (S : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) :
    IsClosed {T : H →WOT[𝕜] H | T.toCLM ∈ S.wotClosure} := by
  change IsClosed
    (((S.comap
      (ContinuousLinearMapWOT.starAlgEquiv (𝕜 := 𝕜) (H := H)).toNonUnitalStarAlgHom
      ).topologicalClosure : NonUnitalStarSubalgebra 𝕜 (H →WOT[𝕜] H)) :
        Set (H →WOT[𝕜] H))
  exact NonUnitalStarSubalgebra.isClosed_topologicalClosure _

end NonUnitalStarSubalgebra

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

set_option maxSynthPendingDepth 4

/-- The canonical isometric inclusion identifies the finite coefficient span with its range in
the concrete operator predual. -/
def vectorFunctionalSpanEquivPredualSpan :
    vectorFunctionalSpan (𝕜 := 𝕜) (E := E) (F := F) ≃ₗ[𝕜]
      vectorFunctionalPredualSpan (𝕜 := 𝕜) (E := E) (F := F) :=
  (vectorFunctionalSpanToPredualₗᵢ
    (𝕜 := 𝕜) (E := E) (F := F)).equivRange.toLinearEquiv

omit [CompleteSpace F] in
@[simp]
lemma coe_vectorFunctionalSpanEquivPredualSpan
    (f : vectorFunctionalSpan (𝕜 := 𝕜) (E := E) (F := F)) :
    ((vectorFunctionalSpanEquivPredualSpan f :
      vectorFunctionalPredualSpan (𝕜 := 𝕜) (E := E) (F := F)) :
        VectorFunctionalPredual 𝕜 E F) = vectorFunctionalSpanToPredual f :=
  rfl

end ContinuousLinearMap

namespace ContinuousLinearMapWOT

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The weak topology induced by the finite coefficient core inside the concrete predual is
canonically Mathlib's weak operator topology. -/
def vectorFunctionalPredualSpanWeakEquiv :
    WeakBilin
      (Ultraweak.testPairing (M := H →L[ℂ] H)
        (ContinuousLinearMap.vectorFunctionalPredualSpan
          (𝕜 := ℂ) (E := H) (F := H))) ≃L[ℂ]
      (H →WOT[ℂ] H) := by
  let e : WeakBilin
      (ContinuousLinearMap.vectorFunctionalPairing
        (𝕜 := ℂ) (E := H) (F := H)) ≃L[ℂ]
      WeakBilin
        (Ultraweak.testPairing (M := H →L[ℂ] H)
          (ContinuousLinearMap.vectorFunctionalPredualSpan
            (𝕜 := ℂ) (E := H) (F := H))) :=
    WeakBilin.congr
      (ContinuousLinearMap.vectorFunctionalPairing
        (𝕜 := ℂ) (E := H) (F := H))
      (.refl ℂ (H →L[ℂ] H))
      ContinuousLinearMap.vectorFunctionalSpanEquivPredualSpan
      (Ultraweak.testPairing (M := H →L[ℂ] H)
        (ContinuousLinearMap.vectorFunctionalPredualSpan
          (𝕜 := ℂ) (E := H) (F := H))) (by
        ext T f
        let g := ContinuousLinearMap.vectorFunctionalSpanEquivPredualSpan.symm f
        have hg : ContinuousLinearMap.vectorFunctionalSpanEquivPredualSpan g = f :=
          ContinuousLinearMap.vectorFunctionalSpanEquivPredualSpan.apply_symm_apply f
        simp only [LinearEquiv.arrowCongr_apply, LinearEquiv.refl_apply,
          ContinuousLinearMap.vectorFunctionalPairing_apply,
          Ultraweak.testPairing_apply,
          ContinuousLinearMap.vectorFunctionalPredual_predualEquivDual_apply_apply]
        change (g : (H →L[ℂ] H) →L[ℂ] ℂ) T =
          (ContinuousLinearMap.vectorFunctionalPredualEquivClosure (f :
            ContinuousLinearMap.VectorFunctionalPredual ℂ H H) :
              (H →L[ℂ] H) →L[ℂ] ℂ) T
        rw [← hg, ContinuousLinearMap.coe_vectorFunctionalSpanEquivPredualSpan,
          ContinuousLinearMap.coe_vectorFunctionalSpanToPredual])
  exact e.symm.trans
    (ContinuousLinearMapWOT.vectorFunctionalWeakEquiv
      (𝕜 := ℂ) (E := H) (F := H))

@[simp]
lemma vectorFunctionalPredualSpanWeakEquiv_apply
    (T : WeakBilin
      (Ultraweak.testPairing (M := H →L[ℂ] H)
        (ContinuousLinearMap.vectorFunctionalPredualSpan
          (𝕜 := ℂ) (E := H) (F := H)))) :
    vectorFunctionalPredualSpanWeakEquiv T =
      ContinuousLinearMapWOT.ofCLM
        (WeakBilin.linearEquiv ℂ
          (Ultraweak.testPairing (M := H →L[ℂ] H)
            (ContinuousLinearMap.vectorFunctionalPredualSpan
              (𝕜 := ℂ) (E := H) (F := H))) T) :=
  rfl

@[simp]
lemma vectorFunctionalPredualSpanWeakEquiv_symm_apply (T : H →WOT[ℂ] H) :
    vectorFunctionalPredualSpanWeakEquiv.symm T =
      (show WeakBilin
        (Ultraweak.testPairing (M := H →L[ℂ] H)
          (ContinuousLinearMap.vectorFunctionalPredualSpan
            (𝕜 := ℂ) (E := H) (F := H))) from T.toCLM) :=
  rfl

end ContinuousLinearMapWOT

namespace Ultraweak

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- For the finite coefficient core in the concrete predual of `B(H)`, transported test-weak
closure is exactly closure in Mathlib's weak operator topology. -/
@[simp]
theorem testWeakClosure_vectorFunctionalPredualSpan_eq_wotClosure
    (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)) :
    testWeakClosure
        (ContinuousLinearMap.vectorFunctionalPredualSpan
          (𝕜 := ℂ) (E := H) (F := H)) (S : Set (H →L[ℂ] H)) =
      (S.wotClosure : Set (H →L[ℂ] H)) := by
  let B := testPairing (M := H →L[ℂ] H)
    (ContinuousLinearMap.vectorFunctionalPredualSpan
      (𝕜 := ℂ) (E := H) (F := H))
  let e := ContinuousLinearMapWOT.vectorFunctionalPredualSpanWeakEquiv (H := H)
  let W : Set (H →WOT[ℂ] H) := {T | T.toCLM ∈ S}
  have hpre : e ⁻¹' W =
      (WeakBilin.linearEquiv ℂ B) ⁻¹' (S : Set (H →L[ℂ] H)) := by
    ext T
    rfl
  ext T
  change (WeakBilin.linearEquiv ℂ B).symm T ∈
      closure ((WeakBilin.linearEquiv ℂ B) ⁻¹' (S : Set (H →L[ℂ] H))) ↔
    ContinuousLinearMapWOT.ofCLM T ∈ closure W
  rw [← hpre]
  have hclosure : closure (e ⁻¹' W) = e ⁻¹' closure W :=
    (e.toHomeomorph.preimage_closure W).symm
  rw [hclosure]
  rfl

end Ultraweak
