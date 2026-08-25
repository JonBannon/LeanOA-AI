module

public import LeanOA.Ultraweak.Basic

@[expose] public section

/-!
# Algebraic maps on ultraweak spaces

This file provides the canonical linear maps induced by multiplication in the underlying normed
algebra. No continuity is asserted here: ultraweak continuity depends on the chosen predual and is
proved separately.
-/

open scoped Ultraweak

namespace Ultraweak

variable {𝕜 M P : Type*} [RCLike 𝕜]
  [NonUnitalNormedRing M] [NormedSpace 𝕜 M]
  [IsScalarTower 𝕜 M M] [SMulCommClass 𝕜 M M]
  [NormedAddCommGroup P] [NormedSpace 𝕜 P] [Predual 𝕜 M P]

/-- Left multiplication, transported explicitly to the ultraweak space and bundled as a linear
map in the multiplier. -/
noncomputable def mulLeftₗ : M →ₗ[𝕜] Module.End 𝕜 (σ(M, P)_𝕜) :=
  (linearEquiv 𝕜 M P).symm.conj.toLinearMap.comp (LinearMap.mul 𝕜 M)

@[simp]
lemma mulLeftₗ_apply (a : M) (x : σ(M, P)_𝕜) :
    mulLeftₗ (P := P) a x = toUltraweak 𝕜 P (a * ofUltraweak x) := rfl

@[simp]
lemma mulLeftₗ_mul (a b : M) :
    mulLeftₗ (𝕜 := 𝕜) (P := P) (a * b) =
      (mulLeftₗ (𝕜 := 𝕜) (P := P) a).comp (mulLeftₗ (P := P) b) := by
  ext x
  rw [← ofUltraweak_inj]
  simp [mul_assoc]

/-- Right multiplication, transported explicitly to the ultraweak space and bundled as a linear
map in the multiplier. -/
noncomputable def mulRightₗ : M →ₗ[𝕜] Module.End 𝕜 (σ(M, P)_𝕜) :=
  (linearEquiv 𝕜 M P).symm.conj.toLinearMap.comp (LinearMap.mul 𝕜 M).flip

@[simp]
lemma mulRightₗ_apply (a : M) (x : σ(M, P)_𝕜) :
    mulRightₗ (P := P) a x = toUltraweak 𝕜 P (ofUltraweak x * a) := rfl

@[simp]
lemma mulRightₗ_mul (a b : M) :
    mulRightₗ (𝕜 := 𝕜) (P := P) (a * b) =
      (mulRightₗ (𝕜 := 𝕜) (P := P) b).comp (mulRightₗ (P := P) a) := by
  ext x
  rw [← ofUltraweak_inj]
  simp [mul_assoc]

lemma mem_ker_mulLeftₗ_iff (a : M) {x : σ(M, P)_𝕜} :
    x ∈ LinearMap.ker (mulLeftₗ (P := P) a) ↔ a * ofUltraweak x = 0 := by
  rw [LinearMap.mem_ker, mulLeftₗ_apply, toUltraweak_eq_zero]

lemma mem_ker_mulRightₗ_iff (a : M) {x : σ(M, P)_𝕜} :
    x ∈ LinearMap.ker (mulRightₗ (P := P) a) ↔ ofUltraweak x * a = 0 := by
  rw [LinearMap.mem_ker, mulRightₗ_apply, toUltraweak_eq_zero]

end Ultraweak
