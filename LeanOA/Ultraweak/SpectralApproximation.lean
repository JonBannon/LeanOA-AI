module

public import LeanOA.Ultraweak.SpectralSum

@[expose] public section

/-!
# Norm approximation by finite spectral sums

This file completes the finite-sum approximation step in the existence part of Sakai, Theorem
1.11.3.  First, it proves convergence for an arbitrary filtered family of spectral divisions whose
mesh tends to zero.  It then supplies a concrete sequence of nested dyadic divisions and applies
the general theorem to their lower and upper spectral sums.

The convergence theorem retains the unbundled division interface from
`LeanOA.Ultraweak.SpectralSum`: a family of cut functions, a band count, and a mesh bound.  Thus it
does not introduce a repository-specific partition type.  The elementary dyadic-grid definitions
are stated for seminormed additive star groups; only their application to spectral sums requires a
W-star algebra.
-/

open Finset Filter

namespace WStarAlgebra

section FilteredFamily

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] [WStarAlgebra M]

/-- Lower spectral sums converge in norm along any filtered family of divisions whose endpoints
eventually contain the spectrum and whose mesh tends to zero. -/
theorem tendsto_lowerSpectralSum
    {I : Type*} {l : Filter I} (a : selfAdjoint M) (cut : I → ℕ → ℝ)
    (bands : I → ℕ) (mesh : I → ℝ)
    (hcut : ∀ᶠ k in l, ∀ i ∈ range (bands k), cut k i ≤ cut k (i + 1))
    (hmesh : ∀ᶠ k in l, ∀ i ∈ range (bands k), cut k (i + 1) - cut k i ≤ mesh k)
    (hleft : ∀ᶠ k in l, cut k 0 ≤ -‖a.1‖)
    (hright : ∀ᶠ k in l, ‖a.1‖ < cut k (bands k))
    (hmesh_zero : Tendsto mesh l (nhds 0)) :
    Tendsto (fun k ↦ lowerSpectralSum a (cut k) (bands k)) l (nhds a.1) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hmesh_zero
  filter_upwards [hcut, hmesh, hleft, hright] with k hk hmk hl hr
  rw [norm_sub_rev]
  exact norm_self_sub_lowerSpectralSum_le a (cut k) (bands k) hk hmk hl hr

/-- Upper spectral sums converge in norm along any filtered family of divisions whose endpoints
eventually contain the spectrum and whose mesh tends to zero. -/
theorem tendsto_upperSpectralSum
    {I : Type*} {l : Filter I} (a : selfAdjoint M) (cut : I → ℕ → ℝ)
    (bands : I → ℕ) (mesh : I → ℝ)
    (hcut : ∀ᶠ k in l, ∀ i ∈ range (bands k), cut k i ≤ cut k (i + 1))
    (hmesh : ∀ᶠ k in l, ∀ i ∈ range (bands k), cut k (i + 1) - cut k i ≤ mesh k)
    (hleft : ∀ᶠ k in l, cut k 0 ≤ -‖a.1‖)
    (hright : ∀ᶠ k in l, ‖a.1‖ < cut k (bands k))
    (hmesh_zero : Tendsto mesh l (nhds 0)) :
    Tendsto (fun k ↦ upperSpectralSum a (cut k) (bands k)) l (nhds a.1) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hmesh_zero
  filter_upwards [hcut, hmesh, hleft, hright] with k hk hmk hl hr
  exact norm_upperSpectralSum_sub_self_le a (cut k) (bands k) hk hmk hl hr

end FilteredFamily

section DyadicDivision

variable {A : Type*} [SeminormedAddCommGroup A] [StarAddMonoid A]

/-- The mesh of the canonical dyadic spectral division at stage `k`.  Its `2 ^ k` bands divide
the interval from `-‖a‖ - 1` to `‖a‖ + 1` uniformly. -/
noncomputable def dyadicSpectralMesh (a : selfAdjoint A) (k : ℕ) : ℝ :=
  (2 * ‖a.1‖ + 2) / (2 : ℝ) ^ k

/-- The `i`th cut in the canonical dyadic spectral division at stage `k`. -/
noncomputable def dyadicSpectralCut (a : selfAdjoint A) (k i : ℕ) : ℝ :=
  -‖a.1‖ - 1 + (i : ℝ) * dyadicSpectralMesh a k

/-- Every canonical dyadic spectral mesh is strictly positive. -/
theorem dyadicSpectralMesh_pos (a : selfAdjoint A) (k : ℕ) :
    0 < dyadicSpectralMesh a k := by
  rw [dyadicSpectralMesh]
  positivity

/-- At a fixed stage, the dyadic spectral cuts are monotone in their index. -/
theorem dyadicSpectralCut_monotone (a : selfAdjoint A) (k : ℕ) :
    Monotone (dyadicSpectralCut a k) := by
  intro i j hij
  rw [dyadicSpectralCut, dyadicSpectralCut]
  gcongr
  exact (dyadicSpectralMesh_pos a k).le

/-- The left endpoint of every canonical dyadic spectral division is `-‖a‖ - 1`. -/
@[simp]
theorem dyadicSpectralCut_zero (a : selfAdjoint A) (k : ℕ) :
    dyadicSpectralCut a k 0 = -‖a.1‖ - 1 := by
  simp [dyadicSpectralCut]

/-- The right endpoint after `2 ^ k` canonical dyadic bands is `‖a‖ + 1`. -/
@[simp]
theorem dyadicSpectralCut_bandCount (a : selfAdjoint A) (k : ℕ) :
    dyadicSpectralCut a k (2 ^ k) = ‖a.1‖ + 1 := by
  rw [dyadicSpectralCut, dyadicSpectralMesh, Nat.cast_pow]
  have hk : (2 : ℝ) ^ k ≠ 0 := by positivity
  field_simp
  ring

/-- Every band in a canonical dyadic spectral division has the declared mesh width. -/
theorem dyadicSpectralCut_succ_sub (a : selfAdjoint A) (k i : ℕ) :
    dyadicSpectralCut a k (i + 1) - dyadicSpectralCut a k i =
      dyadicSpectralMesh a k := by
  simp only [dyadicSpectralCut, Nat.cast_add, Nat.cast_one]
  ring

/-- Passing to the next dyadic stage halves the mesh. -/
theorem dyadicSpectralMesh_succ (a : selfAdjoint A) (k : ℕ) :
    dyadicSpectralMesh a (k + 1) = dyadicSpectralMesh a k / 2 := by
  rw [dyadicSpectralMesh, dyadicSpectralMesh, pow_succ]
  field_simp

/-- The next dyadic division refines the preceding one: its even-indexed cuts are precisely the
old cuts. -/
theorem dyadicSpectralCut_refines (a : selfAdjoint A) (k i : ℕ) :
    dyadicSpectralCut a (k + 1) (2 * i) = dyadicSpectralCut a k i := by
  rw [dyadicSpectralCut, dyadicSpectralCut, dyadicSpectralMesh_succ]
  push_cast
  ring

/-- The meshes of the canonical dyadic spectral divisions tend to zero. -/
theorem tendsto_dyadicSpectralMesh (a : selfAdjoint A) :
    Tendsto (dyadicSpectralMesh a) atTop (nhds 0) := by
  change Tendsto (fun k : ℕ ↦ (2 * ‖a.1‖ + 2) / (2 : ℝ) ^ k) atTop (nhds 0)
  exact tendsto_const_nhds.div_atTop
    (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)

end DyadicDivision

section DyadicConvergence

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] [WStarAlgebra M]

/-- The lower sums for the canonical refining dyadic divisions converge in norm to the original
self-adjoint element. -/
theorem tendsto_lowerSpectralSum_dyadic (a : selfAdjoint M) :
    Tendsto (fun k ↦ lowerSpectralSum a (dyadicSpectralCut a k) (2 ^ k))
      atTop (nhds a.1) := by
  apply tendsto_lowerSpectralSum a (dyadicSpectralCut a) (fun k ↦ 2 ^ k)
    (dyadicSpectralMesh a)
  · exact Eventually.of_forall fun k i _ ↦
      dyadicSpectralCut_monotone a k (Nat.le_succ i)
  · exact Eventually.of_forall fun k i _ ↦
      (dyadicSpectralCut_succ_sub a k i).le
  · exact Eventually.of_forall fun k ↦ by
      rw [dyadicSpectralCut_zero]
      linarith
  · exact Eventually.of_forall fun k ↦ by
      rw [dyadicSpectralCut_bandCount]
      linarith
  · exact tendsto_dyadicSpectralMesh a

/-- The upper sums for the canonical refining dyadic divisions converge in norm to the original
self-adjoint element. -/
theorem tendsto_upperSpectralSum_dyadic (a : selfAdjoint M) :
    Tendsto (fun k ↦ upperSpectralSum a (dyadicSpectralCut a k) (2 ^ k))
      atTop (nhds a.1) := by
  apply tendsto_upperSpectralSum a (dyadicSpectralCut a) (fun k ↦ 2 ^ k)
    (dyadicSpectralMesh a)
  · exact Eventually.of_forall fun k i _ ↦
      dyadicSpectralCut_monotone a k (Nat.le_succ i)
  · exact Eventually.of_forall fun k i _ ↦
      (dyadicSpectralCut_succ_sub a k i).le
  · exact Eventually.of_forall fun k ↦ by
      rw [dyadicSpectralCut_zero]
      linarith
  · exact Eventually.of_forall fun k ↦ by
      rw [dyadicSpectralCut_bandCount]
      linarith
  · exact tendsto_dyadicSpectralMesh a

end DyadicConvergence

end WStarAlgebra
