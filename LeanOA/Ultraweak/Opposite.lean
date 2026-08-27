module

public import LeanOA.Mathlib.Topology.Algebra.Module.WeakBilin
public import LeanOA.Ultraweak.Basic

@[expose] public section

/-!
# Multiplicative opposites and the ultraweak topology

The specified predual of a multiplicative opposite is transported along `unop`. Consequently the
canonical `op` and `unop` maps are homeomorphisms for the corresponding ultraweak topologies.
-/

open scoped Ultraweak

namespace Ultraweak

variable {𝕜 M P : Type*} [RCLike 𝕜]
  [NormedAddCommGroup M] [NormedSpace 𝕜 M]
  [NormedAddCommGroup P] [NormedSpace 𝕜 P] [Predual 𝕜 M P]

/-- The canonical continuous linear equivalence from an ultraweak space to its multiplicative
opposite. -/
noncomputable def opCLE : σ(M, P)_𝕜 ≃L[𝕜] σ(Mᵐᵒᵖ, P)_𝕜 :=
  WeakBilin.congr
    (topDualPairing 𝕜 P ∘ₗ
      (Predual.equivDual (𝕜 := 𝕜) (M := M) (P := P)).toLinearEquiv.toLinearMap)
    (MulOpposite.opLinearEquiv 𝕜)
    (LinearEquiv.refl 𝕜 P)
    (topDualPairing 𝕜 P ∘ₗ
      (Predual.equivDual (𝕜 := 𝕜) (M := Mᵐᵒᵖ) (P := P)).toLinearEquiv.toLinearMap)
    (by rfl)

@[simp]
theorem opCLE_apply (x : σ(M, P)_𝕜) :
    ofUltraweak (opCLE (𝕜 := 𝕜) (M := M) (P := P) x) =
      MulOpposite.op (ofUltraweak x) := by
  rfl

@[simp]
theorem opCLE_symm_apply (x : σ(Mᵐᵒᵖ, P)_𝕜) :
    ofUltraweak ((opCLE (𝕜 := 𝕜) (M := M) (P := P)).symm x) =
      MulOpposite.unop (ofUltraweak x) := by
  rfl

/-- A set is ultraweakly closed if and only if its image under the canonical `op` equivalence is
ultraweakly closed. -/
theorem isClosed_image_opCLE_iff (s : Set (σ(M, P)_𝕜)) :
    IsClosed (opCLE (𝕜 := 𝕜) (M := M) (P := P) '' s) ↔ IsClosed s :=
  (opCLE (𝕜 := 𝕜) (M := M) (P := P)).toHomeomorph.isClosed_image

end Ultraweak
