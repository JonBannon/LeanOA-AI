module

public import LeanOA.CStarAlgebra.Extreme
public import LeanOA.Ultraweak.Dual
public import Mathlib.Analysis.Convex.KreinMilman

@[expose] public section

/-!
# Unitality of dual C-star algebras

This file proves that a non-unital C-star algebra which is a specified dual space is unital, and
provides an explicit closed-submodule transport of that result.
-/

open Metric Set
open scoped ComplexOrder Ultraweak

variable {A M P : Type*}

/-- A non-unital C-star algebra with a specified predual is unital. -/
theorem CStarAlgebra.isUnital_of_predual [NonUnitalCStarAlgebra A]
    [NormedAddCommGroup P] [NormedSpace ℂ P] [Predual ℂ A P] :
    IsUnital A := by
  letI : ContinuousSMul ℝ σ(A, P) := ⟨
    Ultraweak.continuous_of_continuous_eval fun p ↦ by
      convert (Complex.continuous_ofReal.comp continuous_fst).mul
        ((Ultraweak.eval_continuous p).comp continuous_snd) using 1
      ext x
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ),
        ← Ultraweak.linearEquiv_apply ℂ A P, map_smul, Ultraweak.linearEquiv_apply, map_smul]
      rfl⟩
  letI : LocallyConvexSpace ℂ σ(A, P) := Ultraweak.locallyConvexSpace ℂ A P
  letI : LocallyConvexSpace ℝ σ(A, P) :=
    LocallyConvexSpace.to_real ℂ σ(A, P) inferInstance
  let e := (Ultraweak.linearEquiv ℂ A P).restrictScalars ℝ
  have he : (e : σ(A, P) → A) = ofUltraweak := by
    ext x
    exact Ultraweak.linearEquiv_apply ℂ A P x
  let s : Set σ(A, P) := e ⁻¹' closedBall (0 : A) 1
  have hs : e '' s = closedBall (0 : A) 1 := Set.image_preimage_eq _ e.surjective
  have hscomp : IsCompact s := by
    dsimp only [s]
    rw [he]
    exact Ultraweak.isCompact_closedBall ℂ P (0 : A) 1
  rw [CStarAlgebra.isUnital_iff, ← hs, ← image_extremePoints]
  exact (hscomp.extremePoints_nonempty ⟨0, by simp [s]⟩).image e

/-- A non-unital C-star algebra explicitly isometric to an ultraweakly closed submodule of a
specified dual Banach space is unital. -/
theorem CStarAlgebra.isUnital_of_isClosed_submodule [NonUnitalCStarAlgebra A]
    [NormedAddCommGroup M] [NormedSpace ℂ M]
    [NormedAddCommGroup P] [NormedSpace ℂ P] [Predual ℂ M P]
    (N : Submodule ℂ M) (e : A ≃ₗᵢ[ℂ] N)
    (hN : IsClosed (Ultraweak.ofSubmodule (P := P) N : Set σ(M, P))) :
    IsUnital A := by
  letI : Predual ℂ N (P ⧸ Ultraweak.preannihilator (P := P) N) :=
    Ultraweak.closedSubmodulePredual N hN
  letI : Predual ℂ A (P ⧸ Ultraweak.preannihilator (P := P) N) :=
    Predual.congr e
  exact CStarAlgebra.isUnital_of_predual
    (P := P ⧸ Ultraweak.preannihilator (P := P) N)
