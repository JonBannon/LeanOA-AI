module

public import LeanOA.ComplexOrder
public import LeanOA.Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
public import LeanOA.Ultraweak.Dual
public import LeanOA.Ultraweak.ProjectionLattice

@[expose] public section

/-!
# Ultraweak continuity implies normality on projections

This file proves that a positive functional represented by a specified Banach predual preserves
least upper bounds of nonempty directed families of projections. The converse, which needs the
projection-selection and cutoff arguments, is proved separately. The predual remains explicit,
without selecting a `WStarAlgebra` instance.
-/

open Filter Set
open scoped ComplexOrder Topology Ultraweak

variable {M P : Type*} [NonUnitalCStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]

namespace PositiveLinearMap

/-- An ultraweakly continuous positive functional is normal on projections. -/
theorem isNormalOnProjections_of_mem_continuousDual (f : M →ₚ[ℂ] ℂ)
    (hf : f.toContinuousLinearMap ∈ Ultraweak.continuousDual ℂ M P) :
    f.IsNormalOnProjections := by
  letI : IsUnital M := CStarAlgebra.isUnital_of_predual (P := P)
  letI : CStarAlgebra M := IsUnital.toCStarAlgebra
  obtain ⟨g, hg⟩ :=
    (Ultraweak.mem_continuousDual_iff_exists_comp_toUltraweakL f.toContinuousLinearMap).1 hf
  have hg_apply (x : M) : g (toUltraweak ℂ P x) = f x := by
    simpa using congrArg (fun h : StrongDual ℂ M ↦ h x) hg
  intro s hnon hs p hp
  letI : Nonempty s := hnon.to_subtype
  letI : IsDirectedOrder s := ⟨hs.directed_val⟩
  have hlim : Tendsto (fun q : s ↦ f q.1.1) atTop (𝓝 (f p.1)) := by
    rw [← hg_apply p.1]
    exact (g.continuous.continuousAt.tendsto.comp
      (IsStarProjection.tendsto_toUltraweak_of_isLUB s hs hnon hp)).congr'
        (Eventually.of_forall fun q ↦ hg_apply q.1.1)
  have h := isLUB_of_tendsto_atTop (fun (_ _ : s) h ↦ f.monotone h) hlim
  change IsLUB (Set.range ((fun q : {p : M // IsStarProjection p} ↦ f q.1) ∘
    (Subtype.val : s → {p : M // IsStarProjection p}))) (f p.1) at h
  simpa only [Set.range_comp, Subtype.range_coe] using h

end PositiveLinearMap
