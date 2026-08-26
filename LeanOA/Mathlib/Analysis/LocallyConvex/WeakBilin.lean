module

public import LeanOA.Mathlib.Topology.Algebra.Module.WeakBilin
public import LeanOA.Mathlib.Analysis.LocallyConvex.Bounded
public import LeanOA.Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Operator.Bilinear

@[expose] public section

open Bornology Filter

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [AddCommGroup F] [Module 𝕜 F] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

namespace WeakBilin

lemma isVonNBounded_iff (s : Set (WeakBilin B)) :
    IsVonNBounded 𝕜 s ↔ ∀ y, IsVonNBounded 𝕜 (((pairing B).flip y) '' s) :=
  WeakBilin.isInducing B |>.isVonNBounded_iff (pairing B).flip s

variable {B} in
lemma isVonNBounded_iff_bddAbove {s : Set (WeakBilin B)} :
    IsVonNBounded 𝕜 s ↔ ∀ y, BddAbove ((‖(pairing B).flip y ·‖) '' s) := by
  have (y : F) : BddBelow ((‖pairing B · y‖) '' s) := ⟨0, by rintro - ⟨_, -, rfl⟩; positivity⟩
  rw [WeakBilin.isVonNBounded_iff]
  congr! with y
  rw [← Bornology.isBounded_iff_isVonNBounded, NormedSpace.vonNBornology_eq 𝕜,
    ← isBounded_norm_iff, Set.image_image, isBounded_iff_bddBelow_bddAbove]
  simp [this]

end WeakBilin

namespace ContinuousLinearMap

variable {E₁ F₁ V₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [NormedAddCommGroup V₁] [NormedSpace 𝕜 V₁]

/-- Convergence of a norm-bounded family against a dense family of test vectors implies
convergence against every test vector.

This is the uniform approximation argument behind the fact that weak topologies obtained from a
dense subspace of the right coordinate agree on bounded subsets.  It is stated for an arbitrary
bounded bilinear pairing, independently of any duality or operator-algebra structure. -/
theorem tendsto_apply_of_denseRange_of_eventually_norm_le
    {B : E₁ →L[𝕜] F₁ →L[𝕜] 𝕜} {T : V₁ →L[𝕜] F₁} (hT : DenseRange T)
    {α : Type*} {l : Filter α} {u : α → E₁} {x : E₁} {C : ℝ} (hC : 0 ≤ C)
    (hu : ∀ᶠ i in l, ‖u i‖ ≤ C)
    (hlim : ∀ v, Tendsto (fun i ↦ B (u i) (T v)) l (nhds (B x (T v)))) (y : F₁) :
    Tendsto (fun i ↦ B (u i) y) l (nhds (B x y)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let K : ℝ := ‖B‖ * (C + ‖x‖)
  have hK : 0 ≤ K := mul_nonneg (norm_nonneg B) (add_nonneg hC (norm_nonneg x))
  have hdenom : 0 < 2 * (K + 1) := by positivity
  obtain ⟨v, hv⟩ := hT.exists_dist_lt y (div_pos hε hdenom)
  have hv' : ‖y - T v‖ < ε / (2 * (K + 1)) := by simpa [dist_eq_norm] using hv
  have hmiddle := (Metric.tendsto_nhds.mp (hlim v)) (ε / 2) (half_pos hε)
  filter_upwards [hu, hmiddle] with i hi hmiddle_i
  rw [dist_eq_norm] at hmiddle_i ⊢
  have hdecomp :
      B (u i) y - B x y =
        B (u i) (y - T v) + (B (u i) (T v) - B x (T v)) + B x (T v - y) := by
    simp only [map_sub]
    abel
  rw [hdecomp]
  calc
    ‖B (u i) (y - T v) + (B (u i) (T v) - B x (T v)) + B x (T v - y)‖
        ≤ ‖B (u i) (y - T v)‖ + ‖B (u i) (T v) - B x (T v)‖ +
            ‖B x (T v - y)‖ := norm_add₃_le ..
    _ ≤ ‖B‖ * ‖u i‖ * ‖y - T v‖ + ‖B (u i) (T v) - B x (T v)‖ +
            ‖B‖ * ‖x‖ * ‖T v - y‖ := by
      gcongr
      · exact B.le_opNorm₂ _ _
      · exact B.le_opNorm₂ _ _
    _ ≤ ‖B‖ * C * ‖y - T v‖ + ‖B (u i) (T v) - B x (T v)‖ +
            ‖B‖ * ‖x‖ * ‖y - T v‖ := by
      rw [norm_sub_rev (T v) y]
      gcongr
    _ = K * ‖y - T v‖ + ‖B (u i) (T v) - B x (T v)‖ := by
      dsimp only [K]
      ring
    _ < ε / 2 + ε / 2 := by
      gcongr
      calc
        K * ‖y - T v‖ ≤ (K + 1) * ‖y - T v‖ := by
          gcongr
          exact le_add_of_nonneg_right zero_le_one
        _ < (K + 1) * (ε / (2 * (K + 1))) :=
          mul_lt_mul_of_pos_left hv' (by positivity)
        _ = ε / 2 := by field_simp
    _ = ε := by ring

end ContinuousLinearMap

namespace WeakBilin

variable {E₁ F₁ V₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [NormedAddCommGroup V₁] [NormedSpace 𝕜 V₁]

/-- A bounded net which converges for the weak topology induced by a norm-dense family of test
vectors converges for the weak topology induced by all test vectors. -/
theorem tendsto_of_denseRange_of_eventually_norm_le
    {B : E₁ →L[𝕜] F₁ →L[𝕜] 𝕜} {T : V₁ →L[𝕜] F₁} (hT : DenseRange T)
    (hB : Function.Injective B) {α : Type*} {l : Filter α} {u : α → E₁} {x : E₁} {C : ℝ}
    (hC : 0 ≤ C) (hu : ∀ᶠ i in l, ‖u i‖ ≤ C)
    (hlim : Tendsto
      (fun i ↦ show WeakBilin
        ((((ContinuousLinearMap.coeLM 𝕜).comp B.toLinearMap).flip.comp T.toLinearMap).flip)
          from u i) l
      (nhds (show WeakBilin
        ((((ContinuousLinearMap.coeLM 𝕜).comp B.toLinearMap).flip.comp T.toLinearMap).flip)
          from x))) :
    Tendsto (fun i ↦ show WeakBilin ((ContinuousLinearMap.coeLM 𝕜).comp B.toLinearMap)
        from u i) l
      (nhds (show WeakBilin ((ContinuousLinearMap.coeLM 𝕜).comp B.toLinearMap) from x)) := by
  let B₀ : E₁ →ₗ[𝕜] F₁ →ₗ[𝕜] 𝕜 := (ContinuousLinearMap.coeLM 𝕜).comp B.toLinearMap
  have hB₀ : Function.Injective B₀ := fun a b hab ↦ hB <| by
    ext y
    exact DFunLike.congr_fun hab y
  change Tendsto (fun i ↦ (WeakBilin.linearEquiv 𝕜 B₀).symm (u i)) l
    (nhds ((WeakBilin.linearEquiv 𝕜 B₀).symm x))
  change Tendsto
    (fun i ↦ (WeakBilin.linearEquiv 𝕜 (B₀.flip.comp T.toLinearMap).flip).symm (u i)) l
    (nhds ((WeakBilin.linearEquiv 𝕜 (B₀.flip.comp T.toLinearMap).flip).symm x)) at hlim
  apply (WeakBilin.tendsto_iff_forall_eval_tendsto (B := B₀) hB₀).2
  intro y
  apply ContinuousLinearMap.tendsto_apply_of_denseRange_of_eventually_norm_le hT hC hu
  intro v
  exact (WeakBilin.eval_continuous (B₀.flip.comp T.toLinearMap).flip v).tendsto _
    |>.comp hlim

end WeakBilin
