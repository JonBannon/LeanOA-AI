module

public import LeanOA.CStarAlgebra.PositiveLinearFunctional
public import LeanOA.Ultraweak.Normal
public import Mathlib.Order.Zorn

@[expose] public section

/-!
# Cutoff functionals of normal positive functionals

For a positive functional `φ` and an element `p`, the right cutoff of `φ` by `p` is the
functional `x ↦ φ (x * p)`. Cauchy–Schwarz controls its operator norm when `p` is a
projection. Consequently, ultraweak continuity of these cutoffs is preserved by directed
suprema of projections, which supplies the chain condition in the associated Zorn argument.

The cutoff construction and its norm convergence are nonunital. A specified predual enters only
when asking whether a cutoff is ultraweakly continuous; unitality enters only for the cutoff at
`1` and the resulting maximal-projection argument.
-/

open Filter Set
open scoped ComplexOrder Topology

namespace PositiveLinearMap

section NonUnital

variable {M : Type*} [NonUnitalCStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

/-- The continuous linear family of right cutoff functionals `x ↦ φ (x * p)`. -/
noncomputable def cutoff (φ : M →ₚ[ℂ] ℂ) : M →L[ℂ] StrongDual ℂ M :=
  (ContinuousLinearMap.compL ℂ M M ℂ φ.toContinuousLinearMap).comp
    (ContinuousLinearMap.mul ℂ M).flip

@[simp]
theorem cutoff_apply (φ : M →ₚ[ℂ] ℂ) (p x : M) : φ.cutoff p x = φ (x * p) :=
  rfl

@[simp]
theorem cutoff_zero (φ : M →ₚ[ℂ] ℂ) : φ.cutoff 0 = 0 := by
  ext
  simp

@[simp]
theorem cutoff_add (φ : M →ₚ[ℂ] ℂ) (p q : M) :
    φ.cutoff (p + q) = φ.cutoff p + φ.cutoff q :=
  map_add φ.cutoff p q

@[simp]
theorem cutoff_sub (φ : M →ₚ[ℂ] ℂ) (p q : M) :
    φ.cutoff (p - q) = φ.cutoff p - φ.cutoff q :=
  map_sub φ.cutoff p q

/-- The operator norm of a cutoff is controlled by the GNS seminorm of the cutting element. -/
theorem norm_cutoff_le_gnsSeminorm (φ : M →ₚ[ℂ] ℂ) (p : M) :
    ‖φ.cutoff p‖ ≤ √‖φ.toContinuousLinearMap‖ * φ.gnsSeminorm p := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x ↦ ?_
  rw [cutoff_apply]
  calc
    ‖φ (x * p)‖ = ‖φ (x * star (star p))‖ := by rw [star_star]
    _ ≤ √‖φ (x * star x)‖ * √‖φ (star p * star (star p))‖ :=
      φ.cauchy_schwarz_mul_star x (star p)
    _ = √‖φ (x * star x)‖ * φ.gnsSeminorm p := by
      rw [gnsSeminorm_apply, star_star]
    _ ≤ √(‖φ.toContinuousLinearMap‖ * ‖x * star x‖) * φ.gnsSeminorm p := by
      gcongr
      simpa using φ.toContinuousLinearMap.le_opNorm (x * star x)
    _ = (√‖φ.toContinuousLinearMap‖ * φ.gnsSeminorm p) * ‖x‖ := by
      rw [CStarRing.norm_self_mul_star, Real.sqrt_mul (norm_nonneg _),
        ← sq, Real.sqrt_sq (norm_nonneg x)]
      ring

/-- Cauchy–Schwarz bounds the operator norm of a cutoff by a projection. -/
theorem norm_cutoff_le (φ : M →ₚ[ℂ] ℂ) {p : M} (hp : IsStarProjection p) :
    ‖φ.cutoff p‖ ≤ √‖φ.toContinuousLinearMap‖ * √‖φ p‖ := by
  simpa only [gnsSeminorm_apply, hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq] using
    φ.norm_cutoff_le_gnsSeminorm p

/-- The cutoff estimate for the difference of two comparable projections. -/
theorem norm_cutoff_sub_le (φ : M →ₚ[ℂ] ℂ)
    {p q : {p : M // IsStarProjection p}} (hqp : q ≤ p) :
    ‖φ.cutoff (p.1 - q.1)‖ ≤
      √‖φ.toContinuousLinearMap‖ * √‖φ (p.1 - q.1)‖ :=
  φ.norm_cutoff_le <| (q.2.le_iff_sub p.2).mp hqp

/-- Cutoffs along a nonempty directed family of projections converge in operator norm to the
cutoff at any specified least upper bound, provided the functional is normal on projections. -/
theorem IsNormalOnProjections.tendsto_cutoff_of_isLUB {φ : M →ₚ[ℂ] ℂ}
    (hφ : φ.IsNormalOnProjections) (s : Set {p : M // IsStarProjection p})
    (hnon : s.Nonempty) (hs : DirectedOn (· ≤ ·) s) {p : {p : M // IsStarProjection p}}
    (hp : IsLUB s p) :
    Tendsto (fun q : s ↦ φ.cutoff q.1.1) atTop (𝓝 (φ.cutoff p.1)) := by
  letI : Nonempty s := hnon.to_subtype
  letI : IsDirectedOrder s := ⟨hs.directed_val⟩
  have hφlim : Tendsto (fun q : s ↦ φ q.1.1) atTop (𝓝 (φ p.1)) := by
    apply tendsto_atTop_isLUB (hφ.monotone.comp <| Subtype.mono_coe (· ∈ s))
    change IsLUB (Set.range ((fun q : {p : M // IsStarProjection p} ↦ φ q.1) ∘
      (Subtype.val : s → {p : M // IsStarProjection p}))) (φ p.1)
    simpa only [Set.range_comp, Subtype.range_coe] using hφ hnon hs hp
  have hzero : Tendsto (fun q : s ↦ √‖φ (p.1 - q.1.1)‖) atTop (𝓝 0) := by
    have hsub : Tendsto (fun q : s ↦ φ p.1 - φ q.1.1) atTop (𝓝 0) := by
      simpa only [sub_self] using (tendsto_const_nhds (x := φ p.1)).sub hφlim
    have hsqrt := ((Real.continuous_sqrt.comp continuous_norm).tendsto (0 : ℂ)).comp hsub
    change Tendsto (fun q : s ↦ √‖φ p.1 - φ q.1.1‖) atTop (𝓝 (√‖(0 : ℂ)‖)) at hsqrt
    simpa only [map_sub, norm_zero, Real.sqrt_zero] using hsqrt
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (g := fun q : s ↦
    √‖φ.toContinuousLinearMap‖ * √‖φ (p.1 - q.1.1)‖) (fun _ ↦ norm_nonneg _) (fun q ↦ ?_) ?_
  · rw [norm_sub_rev, ← cutoff_sub]
    exact φ.norm_cutoff_sub_le <| hp.1 q.2
  · simpa only [mul_zero] using
      (tendsto_const_nhds (x := √‖φ.toContinuousLinearMap‖)).mul hzero

end NonUnital

section Unital

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

@[simp]
theorem cutoff_one (φ : M →ₚ[ℂ] ℂ) : φ.cutoff 1 = φ.toContinuousLinearMap := by
  ext
  simp

end Unital

section Predual

variable {M P : Type*} [NonUnitalCStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]

/-- A projection has ultraweakly continuous cutoff when its cutoff belongs to the image of the
specified predual in the norm dual. -/
def IsUltraweakCutoff (φ : M →ₚ[ℂ] ℂ) (P : Type*) [NormedAddCommGroup P]
    [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]
    (p : {p : M // IsStarProjection p}) : Prop :=
  φ.cutoff p.1 ∈ Ultraweak.continuousDual ℂ M P

@[simp]
theorem isUltraweakCutoff_zero (φ : M →ₚ[ℂ] ℂ) :
    φ.IsUltraweakCutoff P ⟨0, IsStarProjection.zero M⟩ := by
  simp [IsUltraweakCutoff]

/-- Ultraweak continuity of cutoff functionals is closed under nonempty directed suprema of
projections. -/
theorem IsNormalOnProjections.isUltraweakCutoff_of_isLUB {φ : M →ₚ[ℂ] ℂ}
    (hφ : φ.IsNormalOnProjections) (s : Set {p : M // IsStarProjection p})
    (hnon : s.Nonempty) (hs : DirectedOn (· ≤ ·) s) {p : {p : M // IsStarProjection p}}
    (hp : IsLUB s p) (hcutoff : ∀ q ∈ s, φ.IsUltraweakCutoff P q) :
    φ.IsUltraweakCutoff P p := by
  letI : Nonempty s := hnon.to_subtype
  letI : IsDirectedOrder s := ⟨hs.directed_val⟩
  exact (Ultraweak.continuousDual ℂ M P).isClosed.mem_of_tendsto
    (hφ.tendsto_cutoff_of_isLUB s hnon hs hp)
    (Eventually.of_forall fun q ↦ hcutoff q.1 q.2)

end Predual

section UnitalPredual

variable {M P : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]

/-- A normal positive functional has a maximal projection with ultraweakly continuous cutoff. -/
theorem IsNormalOnProjections.exists_maximal_isUltraweakCutoff {φ : M →ₚ[ℂ] ℂ}
    (hφ : φ.IsNormalOnProjections) :
    ∃ p : {p : M // IsStarProjection p}, Maximal (φ.IsUltraweakCutoff P) p := by
  letI : CompleteLattice {p : M // IsStarProjection p} :=
    IsStarProjection.completeLatticeOfPredual (P := P)
  let pzero : {p : M // IsStarProjection p} := ⟨0, IsStarProjection.zero M⟩
  obtain ⟨p, -, hp⟩ := zorn_le_nonempty₀ {p | φ.IsUltraweakCutoff P p} (fun c hc hchain q hq ↦
    ⟨sSup c, hφ.isUltraweakCutoff_of_isLUB c ⟨q, hq⟩ hchain.directedOn
      (isLUB_sSup c) fun r hr ↦ hc hr, fun r hr ↦ le_sSup hr⟩) pzero
        (by
          change φ.IsUltraweakCutoff P pzero
          simpa only [pzero] using φ.isUltraweakCutoff_zero (P := P))
  exact ⟨p, hp⟩

end UnitalPredual

end PositiveLinearMap
