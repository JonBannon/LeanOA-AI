module

public import LeanOA.Mathlib.Analysis.InnerProductSpace.OperatorPredual
public import Mathlib.Analysis.MeanInequalities

/-!
# Square-summable series of vector functionals

This file integrates separately square-summable families of vector functionals into the
norm-closed coefficient space constructed in `OperatorPredual`.  The results are stated for an
arbitrary index type and at the same generality as the underlying coefficient norm: an `RCLike`
scalar, a seminormed operator domain, and an inner-product codomain.  Completeness of the codomain
is not needed because the coefficient closure itself is complete.
-/

@[expose] public section

open scoped InnerProduct InnerProductSpace

noncomputable section

namespace ContinuousLinearMap

variable {ι 𝕜 E F : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

set_option maxSynthPendingDepth 4

/-- Two separately square-summable vector families give a summable family in the norm-closed
vector-functional space. -/
theorem summable_vectorFunctionalInClosure_of_summable_sq
    (xi : ι → E) (eta : ι → F)
    (hxi : Summable (fun i ↦ ‖xi i‖ ^ 2))
    (heta : Summable (fun i ↦ ‖eta i‖ ^ 2)) :
    Summable (fun i ↦ vectorFunctionalInClosure (𝕜 := 𝕜) (xi i) (eta i)) := by
  apply Summable.of_norm
  simpa only [norm_vectorFunctionalInClosure] using
    (Real.summable_mul_of_Lp_Lq_of_nonneg Real.HolderConjugate.two_two
      (fun i ↦ norm_nonneg (xi i)) (fun i ↦ norm_nonneg (eta i))
      (by simpa only [Real.rpow_two] using hxi)
      (by simpa only [Real.rpow_two] using heta))

/-- The element of the norm-closed vector-functional space represented by a coefficient series.
The useful API assumes separate square summability; the definition itself does not retain proof
arguments. -/
def vectorFunctionalSeries (xi : ι → E) (eta : ι → F) :
    vectorFunctionalClosure (𝕜 := 𝕜) (E := E) (F := F) :=
  ∑' i, vectorFunctionalInClosure (𝕜 := 𝕜) (xi i) (eta i)

/-- Cauchy--Schwarz bound for the norm of a vector-functional series. -/
theorem norm_vectorFunctionalSeries_le (xi : ι → E) (eta : ι → F)
    (hxi : Summable (fun i ↦ ‖xi i‖ ^ 2))
    (heta : Summable (fun i ↦ ‖eta i‖ ^ 2)) :
    ‖vectorFunctionalSeries (𝕜 := 𝕜) xi eta‖ ≤
      √(∑' i, ‖xi i‖ ^ 2) * √(∑' i, ‖eta i‖ ^ 2) := by
  have hnorm : Summable (fun i ↦
      ‖vectorFunctionalInClosure (𝕜 := 𝕜) (xi i) (eta i)‖) := by
    simpa only [norm_vectorFunctionalInClosure] using
      (Real.summable_mul_of_Lp_Lq_of_nonneg Real.HolderConjugate.two_two
        (fun i ↦ norm_nonneg (xi i)) (fun i ↦ norm_nonneg (eta i))
        (by simpa only [Real.rpow_two] using hxi)
        (by simpa only [Real.rpow_two] using heta))
  calc
    ‖vectorFunctionalSeries (𝕜 := 𝕜) xi eta‖ ≤
        ∑' i, ‖vectorFunctionalInClosure (𝕜 := 𝕜) (xi i) (eta i)‖ := by
      exact norm_tsum_le_tsum_norm hnorm
    _ = ∑' i, ‖xi i‖ * ‖eta i‖ := by
      congr 1
      funext i
      exact norm_vectorFunctionalInClosure (xi i) (eta i)
    _ ≤ √(∑' i, ‖xi i‖ ^ 2) * √(∑' i, ‖eta i‖ ^ 2) := by
      simpa only [Real.rpow_two, Real.sqrt_eq_rpow] using
        (Real.inner_le_Lp_mul_Lq_tsum_of_nonneg Real.HolderConjugate.two_two
          (fun i ↦ norm_nonneg (xi i)) (fun i ↦ norm_nonneg (eta i))
          (by simpa only [Real.rpow_two] using hxi)
          (by simpa only [Real.rpow_two] using heta))

/-- A square-summable coefficient series is summable in the ambient operator norm dual. -/
theorem summable_vectorFunctional_of_summable_sq (xi : ι → E) (eta : ι → F)
    (hxi : Summable (fun i ↦ ‖xi i‖ ^ 2))
    (heta : Summable (fun i ↦ ‖eta i‖ ^ 2)) :
    Summable (fun i ↦ vectorFunctional (𝕜 := 𝕜) (xi i) (eta i)) := by
  have h := (summable_vectorFunctionalInClosure_of_summable_sq xi eta hxi heta).map
    (vectorFunctionalClosure (𝕜 := 𝕜) (E := E) (F := F)).subtypeL
    (vectorFunctionalClosure (𝕜 := 𝕜) (E := E) (F := F)).subtypeL.continuous
  apply h.congr
  intro i
  exact coe_vectorFunctionalInClosure (𝕜 := 𝕜) (xi i) (eta i)

/-- The scalar coefficients obtained by applying a bounded map to two separately
square-summable vector families form a summable series. -/
theorem summable_inner_apply_of_summable_sq (T : E →L[𝕜] F)
    (xi : ι → E) (eta : ι → F)
    (hxi : Summable (fun i ↦ ‖xi i‖ ^ 2))
    (heta : Summable (fun i ↦ ‖eta i‖ ^ 2)) :
    Summable (fun i ↦ ⟪eta i, T (xi i)⟫_𝕜) := by
  have h := (summable_vectorFunctionalInClosure_of_summable_sq xi eta hxi heta).map
    (vectorFunctionalClosureEvaluation (𝕜 := 𝕜) T)
    (vectorFunctionalClosureEvaluation (𝕜 := 𝕜) T).continuous
  apply h.congr
  intro i
  simp only [Function.comp_apply, vectorFunctionalClosureEvaluation_apply_apply,
    coe_vectorFunctionalInClosure, vectorFunctional_apply]

/-- Coercing a vector-functional series to the ambient norm dual gives the termwise ambient
series. -/
theorem coe_vectorFunctionalSeries (xi : ι → E) (eta : ι → F)
    (hxi : Summable (fun i ↦ ‖xi i‖ ^ 2))
    (heta : Summable (fun i ↦ ‖eta i‖ ^ 2)) :
    (vectorFunctionalSeries (𝕜 := 𝕜) xi eta : (E →L[𝕜] F) →L[𝕜] 𝕜) =
      ∑' i, vectorFunctional (𝕜 := 𝕜) (xi i) (eta i) := by
  exact ((vectorFunctionalClosure (𝕜 := 𝕜) (E := E) (F := F)).subtypeL.map_tsum
    (summable_vectorFunctionalInClosure_of_summable_sq xi eta hxi heta))

/-- Evaluation of a vector-functional series is the corresponding scalar coefficient series. -/
theorem vectorFunctionalClosureEvaluation_vectorFunctionalSeries
    (T : E →L[𝕜] F) (xi : ι → E) (eta : ι → F)
    (hxi : Summable (fun i ↦ ‖xi i‖ ^ 2))
    (heta : Summable (fun i ↦ ‖eta i‖ ^ 2)) :
    vectorFunctionalClosureEvaluation (𝕜 := 𝕜) T (vectorFunctionalSeries xi eta) =
      ∑' i, ⟪eta i, T (xi i)⟫_𝕜 := by
  unfold vectorFunctionalSeries
  rw [(vectorFunctionalClosureEvaluation (𝕜 := 𝕜) T).map_tsum
    (summable_vectorFunctionalInClosure_of_summable_sq xi eta hxi heta)]
  simp only [vectorFunctionalClosureEvaluation_apply_apply,
    coe_vectorFunctionalInClosure, vectorFunctional_apply]

/-- The source-form Cauchy--Schwarz estimate for a square-summable coefficient series. -/
theorem norm_tsum_inner_apply_le (T : E →L[𝕜] F)
    (xi : ι → E) (eta : ι → F)
    (hxi : Summable (fun i ↦ ‖xi i‖ ^ 2))
    (heta : Summable (fun i ↦ ‖eta i‖ ^ 2)) :
    ‖∑' i, ⟪eta i, T (xi i)⟫_𝕜‖ ≤
      ‖T‖ * √(∑' i, ‖xi i‖ ^ 2) * √(∑' i, ‖eta i‖ ^ 2) := by
  rw [← vectorFunctionalClosureEvaluation_vectorFunctionalSeries T xi eta hxi heta]
  calc
    ‖vectorFunctionalClosureEvaluation (𝕜 := 𝕜) T (vectorFunctionalSeries xi eta)‖ ≤
        ‖vectorFunctionalClosureEvaluation (𝕜 := 𝕜) T‖ *
          ‖vectorFunctionalSeries (𝕜 := 𝕜) xi eta‖ :=
      (vectorFunctionalClosureEvaluation (𝕜 := 𝕜) T).le_opNorm _
    _ = ‖T‖ * ‖vectorFunctionalSeries (𝕜 := 𝕜) xi eta‖ := by
      rw [norm_vectorFunctionalClosureEvaluation]
    _ ≤ ‖T‖ * (√(∑' i, ‖xi i‖ ^ 2) * √(∑' i, ‖eta i‖ ^ 2)) := by
      gcongr
      exact norm_vectorFunctionalSeries_le xi eta hxi heta
    _ = ‖T‖ * √(∑' i, ‖xi i‖ ^ 2) * √(∑' i, ‖eta i‖ ^ 2) := by
      ring

end ContinuousLinearMap
