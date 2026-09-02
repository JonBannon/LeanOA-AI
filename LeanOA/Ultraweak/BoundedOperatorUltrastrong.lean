module

public import LeanOA.Mathlib.Analysis.LocallyConvex.SquareSummableConvergenceCLM
public import LeanOA.Ultraweak.BoundedOperatorCoefficientSeries
public import LeanOA.Ultraweak.Strong
public import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!
# Ultrastrong convergence on bounded operators

For a complex Hilbert space `H`, this file compares Sakai's concrete ultrastrong topology on
`B(H)` with the intrinsic strong topology induced by the canonical concrete predual.

Every square-summable family `ξ` defines the positive normal functional

`T ↦ ∑' n, ⟪ξ n, T (ξ n)⟫`.

Its intrinsic GNS seminorm is exactly `T ↦ √(∑' n, ‖T (ξ n)‖ ^ 2)`. Consequently the identity
from the intrinsic strong carrier to the concrete ultrastrong carrier is continuous. Only this
source-required direction is proved here; the converse and topology equality require Sakai's
later representation theorem for positive normal functionals.
-/

@[expose] public section

open scoped ComplexOrder ENNReal InnerProduct InnerProductSpace lp Ultraweak

noncomputable section

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "BH" => H →L[ℂ] H
local notation "BHPredual" => VectorFunctionalPredual ℂ H H

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
private theorem summable_norm_sq (ξ : ℓ²(ℕ, H)) : Summable (fun n ↦ ‖ξ n‖ ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    (lp.memℓp ξ).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)

/-- The positive ultraweak functional obtained from a diagonal square-summable coefficient
series. -/
def vectorFunctionalDiagonalSeriesUltraweakP
    (ξ : ℓ²(ℕ, H)) : σ(BH, BHPredual) →P[ℂ] ℂ :=
  PositiveContinuousLinearMap.mk₀
    (vectorFunctionalSeriesUltraweakL (fun n ↦ ξ n) (fun n ↦ ξ n)) fun T hT ↦ by
      rw [vectorFunctionalSeriesUltraweakL_apply
        (fun n ↦ ξ n) (fun n ↦ ξ n) (summable_norm_sq ξ) (summable_norm_sq ξ)]
      apply tsum_nonneg
      intro n
      have hpos : ContinuousLinearMap.IsPositive (ofUltraweak T) :=
        (ContinuousLinearMap.nonneg_iff_isPositive _).mp
          (Ultraweak.ofUltraweak_nonneg.mpr hT)
      exact hpos.inner_nonneg_right (ξ n)

@[simp]
theorem vectorFunctionalDiagonalSeriesUltraweakP_apply
    (ξ : ℓ²(ℕ, H)) (T : σ(BH, BHPredual)) :
    vectorFunctionalDiagonalSeriesUltraweakP ξ T =
      ∑' n, ⟪ξ n, (ofUltraweak T) (ξ n)⟫_ℂ := by
  exact vectorFunctionalSeriesUltraweakL_apply
    (fun n ↦ ξ n) (fun n ↦ ξ n) (summable_norm_sq ξ) (summable_norm_sq ξ) T

end ContinuousLinearMap

private theorem boundedOperator_inner_star_mul_self_eq_norm_sq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (x : H) :
    ⟪x, (star T * T) x⟫_ℂ = (‖T x‖ ^ 2 : ℂ) := by
  simp [ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]

namespace BoundedOperatorUltrastrong

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "BH" => H →L[ℂ] H
local notation "BHPredual" => ContinuousLinearMap.VectorFunctionalPredual ℂ H H

/-- The GNS seminorm of a diagonal coefficient-series functional is exactly the corresponding
concrete square-summable application seminorm. -/
theorem gnsSeminorm_vectorFunctionalDiagonalSeriesUltraweakP
    (ξ : ℓ²(ℕ, H)) (T : BH) :
    ((ContinuousLinearMap.vectorFunctionalDiagonalSeriesUltraweakP ξ).comp
      (Ultraweak.toUltraweakPosCLM BHPredual)).toPositiveLinearMap.gnsSeminorm T =
      ContinuousLinearMap.squareSummableSeminorm ξ T := by
  rw [PositiveLinearMap.gnsSeminorm_apply,
    ContinuousLinearMap.squareSummableSeminorm_apply_eq_sqrt_tsum]
  change √‖ContinuousLinearMap.vectorFunctionalDiagonalSeriesUltraweakP ξ
    (toUltraweak ℂ BHPredual (star T * T))‖ = √(∑' n, ‖T (ξ n)‖ ^ 2)
  rw [ContinuousLinearMap.vectorFunctionalDiagonalSeriesUltraweakP_apply]
  simp only [ofUltraweak_toUltraweak]
  have hseries :
      (∑' n, ⟪ξ n, (star T * T) (ξ n)⟫_ℂ) =
        ((∑' n, ‖T (ξ n)‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    congr 1
    funext n
    simpa using boundedOperator_inner_star_mul_self_eq_norm_sq T (ξ n)
  rw [hseries, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (tsum_nonneg fun _ ↦ sq_nonneg _)]

/-- The algebraic identity from the intrinsic strong carrier to the concrete ultrastrong
carrier. -/
def toSquareSummableₗ :
    Ultraweak.Strong BH BHPredual →ₗ[ℂ] (H →USOT[ℂ] H) where
  toFun T := SquareSummableConvergenceCLM.ofCLM (Ultraweak.ofStrong T)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem toSquareSummableₗ_apply (T : Ultraweak.Strong BH BHPredual) :
    SquareSummableConvergenceCLM.toCLM (toSquareSummableₗ T) = Ultraweak.ofStrong T :=
  rfl

/-- The intrinsic strong topology on `B(H)` is finer than the concrete ultrastrong topology. -/
theorem continuous_toSquareSummableₗ :
    Continuous (toSquareSummableₗ (H := H)) := by
  apply SquareSummableConvergenceCLM.withSeminorms.continuous_of_continuous_comp
    toSquareSummableₗ
  intro ξ
  have hs := (Ultraweak.Strong.withSeminorms (M := BH) (P := BHPredual)).continuous_seminorm
    (ContinuousLinearMap.vectorFunctionalDiagonalSeriesUltraweakP ξ)
  refine hs.congr fun T ↦ ?_
  change
    ((ContinuousLinearMap.vectorFunctionalDiagonalSeriesUltraweakP ξ).comp
      (Ultraweak.toUltraweakPosCLM BHPredual)).toPositiveLinearMap.gnsSeminorm
        (Ultraweak.ofStrong T) =
      ContinuousLinearMap.squareSummableSeminorm ξ (Ultraweak.ofStrong T)
  exact gnsSeminorm_vectorFunctionalDiagonalSeriesUltraweakP ξ (Ultraweak.ofStrong T)

/-- The source-safe continuous identity from intrinsic strong convergence on `B(H)` to concrete
ultrastrong convergence. -/
def toSquareSummableL :
    Ultraweak.Strong BH BHPredual →L[ℂ] (H →USOT[ℂ] H) :=
  ⟨toSquareSummableₗ, continuous_toSquareSummableₗ⟩

@[simp]
theorem toSquareSummableL_apply (T : Ultraweak.Strong BH BHPredual) :
    SquareSummableConvergenceCLM.toCLM (toSquareSummableL T) = Ultraweak.ofStrong T :=
  rfl

/-- A concrete-ultrastrong-closed operator set is closed for the intrinsic strong topology. -/
theorem isClosed_strong_of_isClosed_squareSummable (S : Set BH)
    (hS : IsClosed {T : H →USOT[ℂ] H |
      SquareSummableConvergenceCLM.toCLM T ∈ S}) :
    IsClosed {T : Ultraweak.Strong BH BHPredual | Ultraweak.ofStrong T ∈ S} := by
  change IsClosed (toSquareSummableL ⁻¹'
    {T : H →USOT[ℂ] H | SquareSummableConvergenceCLM.toCLM T ∈ S})
  exact hS.preimage toSquareSummableL.continuous

end BoundedOperatorUltrastrong
