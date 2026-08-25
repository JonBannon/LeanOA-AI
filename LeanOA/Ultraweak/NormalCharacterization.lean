module

public import LeanOA.CStarAlgebra.RealRankZero
public import LeanOA.Ultraweak.Corner
public import LeanOA.Ultraweak.Masa
public import LeanOA.Ultraweak.NormalCutoff
public import LeanOA.Ultraweak.NormalSelection
public import LeanOA.Ultraweak.SeparatingDual
public import LeanOA.Ultraweak.Strong

@[expose] public section

/-!
# Order-theoretic characterization of ultraweakly continuous positive functionals

A positive functional on a C-star algebra with a specified Banach predual is ultraweakly
continuous exactly when it preserves directed suprema of projections. The predual remains an
explicit parameter throughout, so the characterization does not depend on a selected
`WStarAlgebra` instance.
-/

open scoped ComplexOrder NNReal Ultraweak
open Ultraweak

variable {M P : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]

namespace PositiveLinearMap

private theorem continuous_strong_cutoff_of_le_on_corner
    (φ : M →ₚ[ℂ] ℂ) (ψ : σ(M, P) →P[ℂ] ℂ) {p : M} (hp : IsStarProjection p)
    (h : ∀ x : hp.Corner, 0 ≤ x →
      φ (IsStarProjection.Corner.inclusionP hp x) ≤
        ψ (toUltraweak ℂ P (IsStarProjection.Corner.inclusionP hp x))) :
    Continuous fun x : s(M, P) ↦ φ.cutoff p (ofStrong x) := by
  let ψp := ψ.comp (IsStarProjection.Corner.ultraweakCutdownP (P := P) hp)
  let c : ℝ≥0 := ⟨√‖φ 1‖, by positivity⟩
  apply Strong.withSeminorms.continuous_normedSpace_rng ℂ
    ((φ.cutoff p).toLinearMap.comp (Strong.linearEquiv M P).toLinearMap)
  refine ⟨{ψp}, c, fun x ↦ ?_⟩
  simp only [Seminorm.comp_apply, Finset.sup_singleton, Strong.seminormFamily,
    Seminorm.smul_apply, NNReal.smul_def]
  change ‖φ (ofStrong x * p)‖ ≤ (c : ℝ) * Strong.seminorm ψp x
  have hφψ :
      φ (p * (star (ofStrong x) * ofStrong x) * p) ≤
        ψ (toUltraweak ℂ P (p * (star (ofStrong x) * ofStrong x) * p)) := by
    simpa only [IsStarProjection.Corner.inclusionP_apply,
      IsStarProjection.Corner.cutdownP_apply,
      IsStarProjection.Corner.coe_cutdownL] using
      h (IsStarProjection.Corner.cutdownP hp (star (ofStrong x) * ofStrong x))
        ((IsStarProjection.Corner.cutdownP hp).map_nonneg
          (star_mul_self_nonneg (ofStrong x)))
  calc
    ‖φ (ofStrong x * p)‖ ≤
        √‖φ (star 1 * 1)‖ *
          √‖φ (star (ofStrong x * p) * (ofStrong x * p))‖ :=
      by simpa only [star_one, one_mul] using
        φ.cauchy_schwarz_star_mul 1 (ofStrong x * p)
    _ = √‖φ 1‖ *
        √‖φ (p * (star (ofStrong x) * ofStrong x) * p)‖ := by
      simp only [star_one, one_mul, star_mul, hp.isSelfAdjoint.star_eq]
      congr 2
      noncomm_ring
    _ ≤ √‖φ 1‖ *
        √‖ψ (toUltraweak ℂ P (p * (star (ofStrong x) * ofStrong x) * p))‖ := by
      gcongr
      exact CStarAlgebra.norm_le_norm_of_nonneg_of_le
        (φ.map_nonneg <| hp.isSelfAdjoint.conjugate_nonneg <| star_mul_self_nonneg (ofStrong x))
        hφψ
    _ = (c : ℝ) * Strong.seminorm ψp x := by
      rw [Strong.seminorm_apply]
      change √‖φ 1‖ *
          √‖ψ (toUltraweak ℂ P (p * (star (ofStrong x) * ofStrong x) * p))‖ =
        (c : ℝ) * √‖ψ (IsStarProjection.Corner.ultraweakCutdownP (P := P) hp
          (toUltraweak ℂ P (star (ofStrong x) * ofStrong x)))‖
      simp only [IsStarProjection.Corner.ultraweakCutdownP_apply,
        ofUltraweak_toUltraweak, c]
      rfl

private theorem mem_continuousDual_of_continuous_strong (f : StrongDual ℂ M)
    (hf : Continuous fun x : s(M, P) ↦ f (ofStrong x)) :
    f ∈ Ultraweak.continuousDual ℂ M P := by
  refine (Ultraweak.mem_continuousDual_iff_exists_comp_toUltraweakL f).2 ⟨⟨
    f.toLinearMap.comp (Ultraweak.linearEquiv ℂ M P).toLinearMap,
    (Strong.continuous_ultraweak_iff_strong f.toLinearMap).2 hf⟩, ?_⟩
  ext x
  simp

/-- A positive functional on a C-star algebra with a specified Banach predual is normal on
projections exactly when it is represented by that predual. -/
theorem isNormalOnProjections_iff_mem_continuousDual (φ : M →ₚ[ℂ] ℂ) :
    φ.IsNormalOnProjections ↔
      φ.toContinuousLinearMap ∈ Ultraweak.continuousDual ℂ M P := by
  constructor
  · intro hφ
    obtain ⟨p₀, hp₀⟩ := hφ.exists_maximal_isUltraweakCutoff (P := P)
    suffices hp₀_one : p₀.1 = 1 by
      have : p₀ = ⟨1, IsStarProjection.one M⟩ := Subtype.ext hp₀_one
      subst p₀
      simpa [IsUltraweakCutoff] using hp₀.1
    by_contra hp₀_one
    let r : {p : M // IsStarProjection p} := ⟨1 - p₀.1, p₀.2.one_sub⟩
    have hr₀ : r.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hp₀_one)
    obtain ⟨ψᵤ, hψᵤ⟩ :=
      Ultraweak.exists_positiveCLM_apply_gt (P := P) φ r.2.nonneg hr₀
    let ψ : M →ₚ[ℂ] ℂ :=
      (ψᵤ.comp (Ultraweak.toUltraweakPosCLM P)).toPositiveLinearMap
    have hψ : ψ.IsNormalOnProjections :=
      ψ.isNormalOnProjections_of_mem_continuousDual <|
        (Ultraweak.mem_continuousDual_iff_exists_comp_toUltraweakL
          ψ.toContinuousLinearMap).2 ⟨ψᵤ.toContinuousLinearMap, by
            ext x
            simp [ψ]⟩
    obtain ⟨p, hp, hp_ne, hpr, hp_lt⟩ :=
      hφ.exists_nonzero_subprojection_lt_of_predual (P := P) hψ r.2 <| by
        change φ r.1 < ψᵤ (toUltraweak ℂ P r.1)
        exact hψᵤ
    let Q := P ⧸ Ultraweak.preannihilator (P := P)
      (IsStarProjection.Corner.rangeSubmodule hp)
    letI : Predual ℂ hp.Corner Q :=
      IsStarProjection.Corner.inducedPredual (P := P) hp
    letI : CStarAlgebra.IsRealRankZero hp.Corner :=
      CStarAlgebra.isRealRankZero_of_predual (P := Q)
    have hcorner (x : hp.Corner) (hx : 0 ≤ x) :
        φ (IsStarProjection.Corner.inclusionP hp x) ≤
          ψᵤ (toUltraweak ℂ P (IsStarProjection.Corner.inclusionP hp x)) := by
      apply PositiveLinearMap.le_on_nonneg_of_le_on_isStarProjection
        (φ.comp (IsStarProjection.Corner.inclusionP hp).toPositiveLinearMap)
        (ψ.comp (IsStarProjection.Corner.inclusionP hp).toPositiveLinearMap)
        (fun q hq ↦ ?_) hx
      by_cases hq₀ : q = 0
      · simp [hq₀]
      · have hqM : IsStarProjection
            ((IsStarProjection.Corner.inclusionP hp).toPositiveLinearMap q) := by
          simpa only [PositiveContinuousLinearMap.coe_toPositiveLinearMap,
            IsStarProjection.Corner.inclusionP_apply,
            IsStarProjection.Corner.inclusion_apply] using
            hq.map (IsStarProjection.Corner.inclusion hp)
        exact (hp_lt hqM (fun h ↦ hq₀ <| IsStarProjection.Corner.ext hp <| by
          simpa only [PositiveContinuousLinearMap.coe_toPositiveLinearMap,
            IsStarProjection.Corner.inclusionP_apply,
            IsStarProjection.Corner.coe_zero] using h)
          (hqM.le_iff_mul_eq_right hp |>.2 <| by
            simpa only [PositiveContinuousLinearMap.coe_toPositiveLinearMap,
              IsStarProjection.Corner.inclusionP_apply] using
              IsStarProjection.Corner.projection_mul hp q)).le
    have hp_cutoff : φ.IsUltraweakCutoff P ⟨p, hp⟩ :=
      mem_continuousDual_of_continuous_strong (φ.cutoff p) <|
        continuous_strong_cutoff_of_le_on_corner φ ψᵤ hp hcorner
    have hp₀p : p₀.1 * p = 0 := by
      rw [← (hp.le_iff_mul_eq_right r.2).mp hpr, ← mul_assoc,
        p₀.2.mul_one_sub_self, zero_mul]
    let q : {p : M // IsStarProjection p} := ⟨p₀.1 + p, p₀.2.add hp hp₀p⟩
    have hq_cutoff : φ.IsUltraweakCutoff P q := by
      rw [IsUltraweakCutoff, show q.1 = p₀.1 + p by rfl, cutoff_add]
      exact (Ultraweak.continuousDual ℂ M P).add_mem hp₀.1 hp_cutoff
    have hp₀q : p₀ ≤ q := by
      change p₀.1 ≤ p₀.1 + p
      exact le_add_of_nonneg_right hp.nonneg
    have hqp₀ := hp₀.2 hq_cutoff hp₀q
    apply hp_ne
    apply add_left_cancel (a := p₀.1)
    simpa only [add_zero, q] using
      (congrArg Subtype.val (hp₀q.antisymm hqp₀)).symm
  · exact φ.isNormalOnProjections_of_mem_continuousDual

end PositiveLinearMap
