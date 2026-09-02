module

public import LeanOA.Ultraweak.BoundedOperator
public import LeanOA.Ultraweak.KaplanskyDensity
public import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!
# The finite vector-functional core as an invariant predual test space

For a complex Hilbert space `H`, this file packages the finite vector-functional span inside the
concrete predual of `B(H)` and verifies the involution and fixed-multiplier invariance required by
`Ultraweak.SakaiInvariantTestSpace`.  The generic inclusion and density API remains in
`Ultraweak.BoundedOperator`; only the operator-algebraic assembly lives here.
-/

@[expose] public section

open scoped InnerProduct InnerProductSpace Ultraweak

noncomputable section

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The abstract predual involution agrees on the finite coefficient core with Mathlib's
intrinsic involution on the operator norm dual. -/
theorem predualStar_vectorFunctionalSpanToPredual
    (f : vectorFunctionalSpan (𝕜 := ℂ) (E := H) (F := H)) :
    Ultraweak.predualStar (M := H →L[ℂ] H)
        (P := VectorFunctionalPredual ℂ H H) (vectorFunctionalSpanToPredual f) =
      vectorFunctionalSpanToPredual
        ⟨(star (WithConv.toConv f.1)).ofConv,
          intrinsicStar_mem_vectorFunctionalSpan f.2⟩ := by
  apply (Predual.toDualₗᵢ (𝕜 := ℂ) (M := H →L[ℂ] H)
    (P := VectorFunctionalPredual ℂ H H)).injective
  ext T
  have h := Ultraweak.pairing_predualStar
    (M := H →L[ℂ] H) (P := VectorFunctionalPredual ℂ H H)
    (toUltraweak ℂ (VectorFunctionalPredual ℂ H H) T)
    (vectorFunctionalSpanToPredual f)
  simpa only [Predual.toDualₗᵢ_apply, Ultraweak.pairing_apply_apply,
    ofUltraweak_toUltraweak, Ultraweak.ofUltraweak_star,
    vectorFunctionalPredual_predualEquivDual_apply_apply,
    coe_vectorFunctionalSpanToPredual,
    ContinuousLinearMap.intrinsicStar_apply] using h

/-- The abstract predual transpose of fixed left multiplication preserves the finite coefficient
core and is represented by precomposition with left multiplication. -/
theorem predualMulLeft_vectorFunctionalSpanToPredual (a : H →L[ℂ] H)
    (f : vectorFunctionalSpan (𝕜 := ℂ) (E := H) (F := H)) :
    Ultraweak.predualMulLeft (P := VectorFunctionalPredual ℂ H H) a
        (vectorFunctionalSpanToPredual f) =
      vectorFunctionalSpanToPredual
        ⟨f.1.comp (ContinuousLinearMap.mulLeftRight ℂ (H →L[ℂ] H) a 1),
          comp_mulLeft_mem_vectorFunctionalSpan a f.2⟩ := by
  apply (Predual.toDualₗᵢ (𝕜 := ℂ) (M := H →L[ℂ] H)
    (P := VectorFunctionalPredual ℂ H H)).injective
  ext T
  have h := Ultraweak.pairing_predualMulLeft
    (M := H →L[ℂ] H) (P := VectorFunctionalPredual ℂ H H) a
    (toUltraweak ℂ (VectorFunctionalPredual ℂ H H) T)
    (vectorFunctionalSpanToPredual f)
  simpa only [Predual.toDualₗᵢ_apply, Ultraweak.pairing_apply_apply,
    ofUltraweak_toUltraweak,
    vectorFunctionalPredual_predualEquivDual_apply_apply,
    coe_vectorFunctionalSpanToPredual,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.mulLeftRight_apply, mul_one] using h

/-- The abstract predual transpose of fixed right multiplication preserves the finite coefficient
core and is represented by precomposition with right multiplication. -/
theorem predualMulRight_vectorFunctionalSpanToPredual (a : H →L[ℂ] H)
    (f : vectorFunctionalSpan (𝕜 := ℂ) (E := H) (F := H)) :
    Ultraweak.predualMulRight (P := VectorFunctionalPredual ℂ H H) a
        (vectorFunctionalSpanToPredual f) =
      vectorFunctionalSpanToPredual
        ⟨f.1.comp (ContinuousLinearMap.mulLeftRight ℂ (H →L[ℂ] H) 1 a),
          comp_mulRight_mem_vectorFunctionalSpan a f.2⟩ := by
  apply (Predual.toDualₗᵢ (𝕜 := ℂ) (M := H →L[ℂ] H)
    (P := VectorFunctionalPredual ℂ H H)).injective
  ext T
  have h := Ultraweak.pairing_predualMulRight
    (M := H →L[ℂ] H) (P := VectorFunctionalPredual ℂ H H) a
    (toUltraweak ℂ (VectorFunctionalPredual ℂ H H) T)
    (vectorFunctionalSpanToPredual f)
  simpa only [Predual.toDualₗᵢ_apply, Ultraweak.pairing_apply_apply,
    ofUltraweak_toUltraweak,
    vectorFunctionalPredual_predualEquivDual_apply_apply,
    coe_vectorFunctionalSpanToPredual,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.mulLeftRight_apply, one_mul] using h

/-- The finite vector-functional core of the concrete predual of `B(H)` is a norm-dense,
involution- and multiplier-invariant Sakai test space. -/
theorem vectorFunctionalPredualSpan_sakaiInvariant :
    Ultraweak.SakaiInvariantTestSpace (M := H →L[ℂ] H)
      (vectorFunctionalPredualSpan (𝕜 := ℂ) (E := H) (F := H)) where
  dense := dense_vectorFunctionalPredualSpan
  predualStar_mem p := by
    obtain ⟨f, hf⟩ := p.2
    rw [← hf]
    change Ultraweak.predualStar (M := H →L[ℂ] H)
      (P := VectorFunctionalPredual ℂ H H) (vectorFunctionalSpanToPredual f) ∈
        vectorFunctionalPredualSpan (𝕜 := ℂ) (E := H) (F := H)
    rw [predualStar_vectorFunctionalSpanToPredual]
    exact ⟨_, rfl⟩
  predualMulLeft_mem a p := by
    obtain ⟨f, hf⟩ := p.2
    rw [← hf]
    change Ultraweak.predualMulLeft (P := VectorFunctionalPredual ℂ H H) a
      (vectorFunctionalSpanToPredual f) ∈
        vectorFunctionalPredualSpan (𝕜 := ℂ) (E := H) (F := H)
    rw [predualMulLeft_vectorFunctionalSpanToPredual]
    exact ⟨_, rfl⟩
  predualMulRight_mem a p := by
    obtain ⟨f, hf⟩ := p.2
    rw [← hf]
    change Ultraweak.predualMulRight (P := VectorFunctionalPredual ℂ H H) a
      (vectorFunctionalSpanToPredual f) ∈
        vectorFunctionalPredualSpan (𝕜 := ℂ) (E := H) (F := H)
    rw [predualMulRight_vectorFunctionalSpanToPredual]
    exact ⟨_, rfl⟩

end ContinuousLinearMap
