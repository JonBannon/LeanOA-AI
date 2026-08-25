module

public import LeanOA.Ultraweak.Dual
public import Mathlib.Analysis.VonNeumannAlgebra.Basic

/-!
# Chosen preduals of W-star algebras

This file connects Mathlib's proposition-valued `WStarAlgebra` class, which asserts the existence of
a Banach predual, with LeanOA's `Predual` class, which records a particular linear isometric
duality. The latter is the interface used to define the ultraweak topology.
-/

@[expose] public section

universe u

namespace WStarAlgebra

open scoped Ultraweak

/-- A C-star algebra with an explicitly specified Banach predual is a W-star algebra. -/
theorem of_predual (P : Type u) (M : Type u) [CStarAlgebra M] [NormedAddCommGroup P]
    [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P] : WStarAlgebra M := by
  refine ⟨⟨P, inferInstance, inferInstance, inferInstance, ?_⟩⟩
  exact ⟨Predual.equivDual.symm.trans (starₗᵢ ℂ)⟩

/-- A Banach space together with a conjugate-linear isometric identification of its dual with a
C-star algebra. -/
structure ChosenPredual (M : Type u) [CStarAlgebra M] where
  /-- The underlying type of the chosen predual. -/
  space : Type u
  /-- The normed additive group structure on the chosen predual. -/
  [normedAddCommGroup : NormedAddCommGroup space]
  /-- The complex normed-space structure on the chosen predual. -/
  [normedSpace : NormedSpace ℂ space]
  /-- Completeness of the chosen predual. -/
  [completeSpace : CompleteSpace space]
  /-- The conjugate-linear isometric identification of the dual with the algebra. -/
  equiv : StrongDual ℂ space ≃ₗᵢ⋆[ℂ] M

/-- The Banach predual selected by classical choice from a `WStarAlgebra` instance. -/
noncomputable def chosenPredual (M : Type u) [CStarAlgebra M] [WStarAlgebra M] :
    ChosenPredual M :=
  Classical.choice <| by
    rcases WStarAlgebra.exists_predual (M := M) with ⟨X, i₁, i₂, i₃, ⟨e⟩⟩
    letI := i₁
    letI := i₂
    letI := i₃
    exact ⟨{ space := X, equiv := e }⟩

/-- A chosen Banach predual of a W-star algebra. -/
noncomputable def predual (M : Type u) [CStarAlgebra M] [WStarAlgebra M] :=
  (chosenPredual M).space

noncomputable instance (M : Type u) [CStarAlgebra M] [WStarAlgebra M] :
    NormedAddCommGroup (predual M) :=
  (chosenPredual M).normedAddCommGroup

noncomputable instance (M : Type u) [CStarAlgebra M] [WStarAlgebra M] :
    NormedSpace ℂ (predual M) :=
  (chosenPredual M).normedSpace

noncomputable instance (M : Type u) [CStarAlgebra M] [WStarAlgebra M] :
    CompleteSpace (predual M) :=
  (chosenPredual M).completeSpace

/-- The canonical linear isometric identification of a W-star algebra with the dual of its chosen
predual. It is obtained by composing Mathlib's conjugate-linear identification with star. -/
noncomputable def predualEquiv (M : Type u) [CStarAlgebra M] [WStarAlgebra M] :
    M ≃ₗᵢ[ℂ] StrongDual ℂ (predual M) :=
  ((chosenPredual M).equiv.trans (starₗᵢ ℂ)).symm

noncomputable instance (M : Type u) [CStarAlgebra M] [WStarAlgebra M] :
    Predual ℂ M (predual M) :=
  ⟨predualEquiv M⟩

/-- A C-star algebra explicitly isometric to an ultraweakly closed submodule of a specified dual
Banach space is a W-star algebra. Its predual is the quotient by the preannihilator. The explicit
isometry prevents any dependence on definitional equality between the ambient subtype structures
and the C-star algebra structures. -/
theorem of_isClosed_submodule (A P M : Type u) [CStarAlgebra A]
    [NormedAddCommGroup M] [NormedSpace ℂ M]
    [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]
    (N : Submodule ℂ M) (e : A ≃ₗᵢ[ℂ] N)
    (hN : IsClosed (Ultraweak.ofSubmodule (P := P) N : Set σ(M, P))) :
    WStarAlgebra A := by
  let hpre : Predual ℂ A (P ⧸ Ultraweak.preannihilator (P := P) N) :=
    ⟨e.trans (Ultraweak.closedSubmoduleEquivDual N hN)⟩
  exact @of_predual (P ⧸ Ultraweak.preannihilator (P := P) N) A inferInstance
    inferInstance inferInstance inferInstance hpre

end WStarAlgebra
