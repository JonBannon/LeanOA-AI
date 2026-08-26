module

public import LeanOA.Ultraweak.NormalCharacterization
public import LeanOA.Ultraweak.PolarDecomposition

@[expose] public section

/-!
# Uniqueness of preduals of non-unital C-star algebras

Any two specified Banach preduals of a non-unital C-star algebra represent the same norm-continuous
functionals. Consequently, matching represented functionals gives a canonical linear isometry
between the two preduals.
-/

open scoped ComplexOrder ComplexStarModule Ultraweak

namespace Ultraweak

noncomputable section

section Unital

variable {M P Q : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]
  [NormedAddCommGroup Q] [NormedSpace ℂ Q] [CompleteSpace Q] [Predual ℂ M Q]

private theorem comp_toUltraweakL_mem_continuousDual_of_isSelfAdjoint
    (f : StrongDual ℂ σ(M, P)) (hf : IsSelfAdjoint (WithConv.toConv f)) :
    f.comp (toUltraweakL ℂ M P) ∈ continuousDual ℂ M Q := by
  obtain ⟨u, φ, -, -, hφ⟩ := exists_positive_comp_mulLeft_of_isSelfAdjoint f hf
  let φM : M →ₚ[ℂ] ℂ :=
    (φ.comp (toUltraweakPosCLM P)).toPositiveLinearMap
  have hφM : φM.IsNormalOnProjections :=
    φM.isNormalOnProjections_of_mem_continuousDual <|
      (mem_continuousDual_iff_exists_comp_toUltraweakL φM.toContinuousLinearMap).2
        ⟨φ.toContinuousLinearMap, by ext; simp [φM]⟩
  have hφMQ : φM.toContinuousLinearMap ∈ continuousDual ℂ M Q :=
    (φM.isNormalOnProjections_iff_mem_continuousDual (P := Q)).1 hφM
  obtain ⟨ψ, hψ⟩ :=
    (mem_continuousDual_iff_exists_comp_toUltraweakL φM.toContinuousLinearMap).1 hφMQ
  have hψ_apply (x : M) : ψ (toUltraweak ℂ Q x) = φM x := by
    simpa using congrArg (fun g : StrongDual ℂ M ↦ g x) hψ
  refine (mem_continuousDual_iff_exists_comp_toUltraweakL
    (f.comp (toUltraweakL ℂ M P))).2 ⟨ψ.comp (mulLeftL (P := Q) u), ?_⟩
  ext x
  calc
    ψ (mulLeftL (P := Q) u (toUltraweak ℂ Q x)) = ψ (toUltraweak ℂ Q (u * x)) := by simp
    _ = φM (u * x) := hψ_apply _
    _ = φ (toUltraweak ℂ P (u * x)) := by simp [φM]
    _ = φ (mulLeftL (P := P) u (toUltraweak ℂ P x)) := by simp
    _ = f (toUltraweak ℂ P x) := by
      simpa using congrArg (fun g : StrongDual ℂ σ(M, P) ↦ g (toUltraweak ℂ P x)) hφ |>.symm

private theorem continuousDual_le :
    continuousDual ℂ M P ≤ continuousDual ℂ M Q := by
  intro f hf
  obtain ⟨g, rfl⟩ :=
    (mem_continuousDual_iff_exists_comp_toUltraweakL f).1 hf
  let gr : StrongDual ℂ σ(M, P) := (ℜ (WithConv.toConv g)).1.ofConv
  let gi : StrongDual ℂ σ(M, P) := (ℑ (WithConv.toConv g)).1.ofConv
  have hgr : IsSelfAdjoint (WithConv.toConv gr) := by
    change IsSelfAdjoint (ℜ (WithConv.toConv g)).1
    exact (ℜ (WithConv.toConv g)).2
  have hgi : IsSelfAdjoint (WithConv.toConv gi) := by
    change IsSelfAdjoint (ℑ (WithConv.toConv g)).1
    exact (ℑ (WithConv.toConv g)).2
  have hg : gr + Complex.I • gi = g := by
    simpa [gr, gi] using congrArg WithConv.ofConv
      (realPart_add_I_smul_imaginaryPart (WithConv.toConv g))
  rw [← hg, ContinuousLinearMap.add_comp, ContinuousLinearMap.smul_comp]
  exact (continuousDual ℂ M Q).add_mem
    (comp_toUltraweakL_mem_continuousDual_of_isSelfAdjoint gr hgr)
    ((continuousDual ℂ M Q).smul_mem Complex.I <|
      comp_toUltraweakL_mem_continuousDual_of_isSelfAdjoint gi hgi)

end Unital

section NonUnital

variable {M P Q : Type*} [NonUnitalCStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]
  [NormedAddCommGroup Q] [NormedSpace ℂ Q] [CompleteSpace Q] [Predual ℂ M Q]

/-- The norm-continuous functionals represented by a non-unital C-star algebra predual are
independent of the specified predual. -/
theorem continuousDual_eq : continuousDual ℂ M P = continuousDual ℂ M Q := by
  letI : IsUnital M := CStarAlgebra.isUnital_of_predual (P := P)
  letI : CStarAlgebra M := IsUnital.toCStarAlgebra
  exact le_antisymm continuousDual_le continuousDual_le

end NonUnital

end

end Ultraweak

namespace Ultraweak


section Uniqueness

variable {M P Q : Type*} [NonUnitalCStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]
  [NormedAddCommGroup Q] [NormedSpace ℂ Q] [CompleteSpace Q] [Predual ℂ M Q]

/-- The identity isometry between the norm-dual images of two specified preduals. -/
noncomputable def continuousDualCongr :
    (continuousDual ℂ M P).toSubmodule ≃ₗᵢ[ℂ]
      (continuousDual ℂ M Q).toSubmodule :=
  LinearIsometryEquiv.ofEq
    (continuousDual ℂ M P).toSubmodule
    (continuousDual ℂ M Q).toSubmodule <|
      congrArg ClosedSubmodule.toSubmodule continuousDual_eq

end Uniqueness

end Ultraweak

namespace Predual

section Uniqueness

variable {M P Q : Type*} [NonUnitalCStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]
  [NormedAddCommGroup Q] [NormedSpace ℂ Q] [CompleteSpace Q] [Predual ℂ M Q]

/-- The canonical linear isometry between two specified Banach preduals of the same non-unital
C-star algebra. It is characterized by representing the same functional on the algebra. -/
noncomputable def equiv : P ≃ₗᵢ[ℂ] Q :=
  (continuousDualEquiv (𝕜 := ℂ) (M := M) (P := P)).trans <|
    (Ultraweak.continuousDualCongr (M := M) (P := P) (Q := Q)).trans
      (continuousDualEquiv (𝕜 := ℂ) (M := M) (P := Q)).symm

/-- The canonical equivalence between specified preduals preserves their represented norm-dual
functionals. -/
@[simp]
theorem toDualₗᵢ_equiv (p : P) :
    toDualₗᵢ (𝕜 := ℂ) (M := M) (P := Q) (equiv (M := M) (P := P) (Q := Q) p) =
      toDualₗᵢ (𝕜 := ℂ) (M := M) (P := P) p := by
  change (((continuousDualEquiv (𝕜 := ℂ) (M := M) (P := Q))
      (equiv (M := M) (P := P) (Q := Q) p) :
      (Ultraweak.continuousDual ℂ M Q).toSubmodule) : StrongDual ℂ M) =
    (((continuousDualEquiv (𝕜 := ℂ) (M := M) (P := P)) p :
      (Ultraweak.continuousDual ℂ M P).toSubmodule) : StrongDual ℂ M)
  rw [show equiv (M := M) (P := P) (Q := Q) p =
      (continuousDualEquiv (𝕜 := ℂ) (M := M) (P := Q)).symm
        (Ultraweak.continuousDualCongr (M := M) (P := P) (Q := Q)
          (continuousDualEquiv (𝕜 := ℂ) (M := M) (P := P) p)) by rfl,
    LinearIsometryEquiv.apply_symm_apply]
  exact LinearIsometryEquiv.coe_ofEq_apply _ _

/-- The canonical equivalence between specified preduals preserves the original dual pairings. -/
@[simp]
theorem equiv_apply_duality (p : P) (x : M) :
    Predual.equivDual (𝕜 := ℂ) (M := M) (P := Q) x (equiv (M := M) p) =
      Predual.equivDual (𝕜 := ℂ) (M := M) (P := P) x p := by
  simpa only [toDualₗᵢ_apply] using congrArg (fun f : StrongDual ℂ M ↦ f x) (toDualₗᵢ_equiv p)

/-- The pairing-preservation property uniquely determines the canonical equivalence of specified
preduals. -/
theorem equiv_eq_of_apply_duality_eq (e : P ≃ₗᵢ[ℂ] Q)
    (he : ∀ p x, Predual.equivDual (𝕜 := ℂ) (M := M) (P := Q) x (e p) =
      Predual.equivDual (𝕜 := ℂ) (M := M) (P := P) x p) :
    e = equiv (M := M) (P := P) (Q := Q) := by
  ext p
  apply (toDualₗᵢ (𝕜 := ℂ) (M := M) (P := Q)).injective
  ext x
  rw [toDualₗᵢ_apply, toDualₗᵢ_equiv]
  exact he p x

end Uniqueness

end Predual
