module

public import LeanOA.Ultraweak.SpectralApproximation

@[expose] public section

/-!
# Tagged finite sums for a spectral resolution

This file defines finite spectral sums whose coefficient in each band is an arbitrary tag between
the adjacent cuts. Such a sum lies between the existing lower and upper spectral sums. Hence, when
the cuts contain the spectrum, its norm error is bounded by the mesh and tagged sums converge along
every mesh-zero family of divisions.

The interface retains the unbundled cut and band-count conventions of
`LeanOA.Ultraweak.SpectralSum`. It introduces neither a partition structure nor a set-indexed
spectral resolution.
-/

open Finset Filter
open scoped BigOperators

namespace WStarAlgebra

section FiniteSum

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] [WStarAlgebra M]

/-- The tagged finite sum for the first `n` bands of a spectral family. -/
noncomputable def taggedSpectralSum
    (a : selfAdjoint M) (cut tag : ℕ → ℝ) (n : ℕ) : M :=
  ∑ i ∈ range n,
    tag i • ((spectralProjectionIio a (cut (i + 1))).1 -
      (spectralProjectionIio a (cut i)).1)

/-- Tagging every band by its left endpoint recovers the lower spectral sum. -/
@[simp]
theorem taggedSpectralSum_eq_lowerSpectralSum
    (a : selfAdjoint M) (cut : ℕ → ℝ) (n : ℕ) :
    taggedSpectralSum a cut cut n = lowerSpectralSum a cut n :=
  rfl

/-- Tagging every band by its right endpoint recovers the upper spectral sum. -/
@[simp]
theorem taggedSpectralSum_eq_upperSpectralSum
    (a : selfAdjoint M) (cut : ℕ → ℝ) (n : ℕ) :
    taggedSpectralSum a cut (fun i ↦ cut (i + 1)) n = upperSpectralSum a cut n :=
  rfl

/-- Every tagged spectral sum is self-adjoint. -/
theorem isSelfAdjoint_taggedSpectralSum
    (a : selfAdjoint M) (cut tag : ℕ → ℝ) (n : ℕ) :
    IsSelfAdjoint (taggedSpectralSum a cut tag n) := by
  rw [taggedSpectralSum]
  apply isSelfAdjoint_sum
  intro i hi
  exact (isSelfAdjoint_iff.mpr (star_trivial (tag i))).smul
    ((spectralProjectionIio a (cut (i + 1))).2.isSelfAdjoint.sub
      (spectralProjectionIio a (cut i)).2.isSelfAdjoint)

/-- Choosing each tag above its band's left endpoint bounds the lower spectral sum by the tagged
sum. -/
theorem lowerSpectralSum_le_taggedSpectralSum
    (a : selfAdjoint M) (cut tag : ℕ → ℝ) (n : ℕ)
    (hcut : ∀ i ∈ range n, cut i ≤ cut (i + 1))
    (htag : ∀ i ∈ range n, cut i ≤ tag i) :
    lowerSpectralSum a cut n ≤ taggedSpectralSum a cut tag n := by
  rw [lowerSpectralSum, taggedSpectralSum]
  exact Finset.sum_le_sum fun i hi ↦
    smul_le_smul_of_nonneg_right (htag i hi)
      (sub_nonneg.mpr (spectralProjectionIio_mono a (hcut i hi)))

/-- Choosing each tag below its band's right endpoint bounds the tagged spectral sum by the upper
spectral sum. -/
theorem taggedSpectralSum_le_upperSpectralSum
    (a : selfAdjoint M) (cut tag : ℕ → ℝ) (n : ℕ)
    (hcut : ∀ i ∈ range n, cut i ≤ cut (i + 1))
    (htag : ∀ i ∈ range n, tag i ≤ cut (i + 1)) :
    taggedSpectralSum a cut tag n ≤ upperSpectralSum a cut n := by
  rw [taggedSpectralSum, upperSpectralSum]
  exact Finset.sum_le_sum fun i hi ↦
    smul_le_smul_of_nonneg_right (htag i hi)
      (sub_nonneg.mpr (spectralProjectionIio_mono a (hcut i hi)))

/-- Tags lying in their adjacent cut intervals place the tagged sum between the lower and upper
spectral sums. -/
theorem lowerSpectralSum_le_taggedSpectralSum_and_taggedSpectralSum_le_upperSpectralSum
    (a : selfAdjoint M) (cut tag : ℕ → ℝ) (n : ℕ)
    (htag : ∀ i ∈ range n, cut i ≤ tag i ∧ tag i ≤ cut (i + 1)) :
    lowerSpectralSum a cut n ≤ taggedSpectralSum a cut tag n ∧
      taggedSpectralSum a cut tag n ≤ upperSpectralSum a cut n := by
  have hcut : ∀ i ∈ range n, cut i ≤ cut (i + 1) :=
    fun i hi ↦ (htag i hi).1.trans (htag i hi).2
  exact ⟨lowerSpectralSum_le_taggedSpectralSum a cut tag n hcut fun i hi ↦ (htag i hi).1,
    taggedSpectralSum_le_upperSpectralSum a cut tag n hcut fun i hi ↦ (htag i hi).2⟩

/-- If the endpoint cuts contain the spectrum, the error of a tagged spectral sum is no larger
than the gap between the corresponding upper and lower sums. -/
theorem norm_taggedSpectralSum_sub_self_le_norm_upperSpectralSum_sub_lowerSpectralSum
    (a : selfAdjoint M) (cut tag : ℕ → ℝ) (n : ℕ)
    (htag : ∀ i ∈ range n, cut i ≤ tag i ∧ tag i ≤ cut (i + 1))
    (hleft : cut 0 ≤ -‖a.1‖) (hright : ‖a.1‖ < cut n) :
    ‖taggedSpectralSum a cut tag n - a.1‖ ≤
      ‖upperSpectralSum a cut n - lowerSpectralSum a cut n‖ := by
  have hcut : ∀ i ∈ range n, cut i ≤ cut (i + 1) :=
    fun i hi ↦ (htag i hi).1.trans (htag i hi).2
  have htagged :=
    lowerSpectralSum_le_taggedSpectralSum_and_taggedSpectralSum_le_upperSpectralSum
      a cut tag n htag
  have ha := lowerSpectralSum_le_self_and_self_le_upperSpectralSum
    a cut n hcut hleft hright
  have hlowerUpper :
      IsSelfAdjoint (lowerSpectralSum a cut n - upperSpectralSum a cut n) :=
    (isSelfAdjoint_lowerSpectralSum a cut n).sub
      (isSelfAdjoint_upperSpectralSum a cut n)
  calc
    ‖taggedSpectralSum a cut tag n - a.1‖ ≤
        max ‖lowerSpectralSum a cut n - upperSpectralSum a cut n‖
          ‖upperSpectralSum a cut n - lowerSpectralSum a cut n‖ :=
      hlowerUpper.norm_le_max_of_le_of_le
        (sub_le_sub htagged.1 ha.2) (sub_le_sub htagged.2 ha.1)
    _ = ‖upperSpectralSum a cut n - lowerSpectralSum a cut n‖ := by
      rw [norm_sub_rev]
      simp

/-- A tagged spectral sum whose tags lie in adjacent cut intervals approximates the original
self-adjoint element with error at most the mesh. -/
theorem norm_taggedSpectralSum_sub_self_le
    (a : selfAdjoint M) (cut tag : ℕ → ℝ) (n : ℕ) {δ : ℝ}
    (htag : ∀ i ∈ range n, cut i ≤ tag i ∧ tag i ≤ cut (i + 1))
    (hmesh : ∀ i ∈ range n, cut (i + 1) - cut i ≤ δ)
    (hleft : cut 0 ≤ -‖a.1‖) (hright : ‖a.1‖ < cut n) :
    ‖taggedSpectralSum a cut tag n - a.1‖ ≤ δ := by
  have hcut : ∀ i ∈ range n, cut i ≤ cut (i + 1) :=
    fun i hi ↦ (htag i hi).1.trans (htag i hi).2
  exact (norm_taggedSpectralSum_sub_self_le_norm_upperSpectralSum_sub_lowerSpectralSum
    a cut tag n htag hleft hright).trans
      (norm_upperSpectralSum_sub_lowerSpectralSum_le
        a cut n hcut hmesh hleft hright)

end FiniteSum

section FilteredFamily

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] [WStarAlgebra M]

/-- Tagged spectral sums converge in norm along any filtered family whose tags lie in their
adjacent cut intervals, whose endpoints eventually contain the spectrum, and whose mesh tends to
zero. -/
theorem tendsto_taggedSpectralSum
    {I : Type*} {l : Filter I} (a : selfAdjoint M) (cut tag : I → ℕ → ℝ)
    (bands : I → ℕ) (mesh : I → ℝ)
    (htag : ∀ᶠ k in l, ∀ i ∈ range (bands k),
      cut k i ≤ tag k i ∧ tag k i ≤ cut k (i + 1))
    (hmesh : ∀ᶠ k in l, ∀ i ∈ range (bands k),
      cut k (i + 1) - cut k i ≤ mesh k)
    (hleft : ∀ᶠ k in l, cut k 0 ≤ -‖a.1‖)
    (hright : ∀ᶠ k in l, ‖a.1‖ < cut k (bands k))
    (hmesh_zero : Tendsto mesh l (nhds 0)) :
    Tendsto (fun k ↦ taggedSpectralSum a (cut k) (tag k) (bands k)) l (nhds a.1) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hmesh_zero
  filter_upwards [htag, hmesh, hleft, hright] with k htk hmk hl hr
  exact norm_taggedSpectralSum_sub_self_le a (cut k) (tag k) (bands k) htk hmk hl hr

/-- Tagged spectral sums also converge in every specified ultraweak topology.  This is a direct
corollary of the stronger norm convergence theorem and makes the topology in Sakai's
Radon--Stieltjes formulation explicit without introducing an integral object. -/
theorem tendsto_taggedSpectralSum_ultraweak
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] [Predual ℂ M P]
    {I : Type*} {l : Filter I} (a : selfAdjoint M) (cut tag : I → ℕ → ℝ)
    (bands : I → ℕ) (mesh : I → ℝ)
    (htag : ∀ᶠ k in l, ∀ i ∈ range (bands k),
      cut k i ≤ tag k i ∧ tag k i ≤ cut k (i + 1))
    (hmesh : ∀ᶠ k in l, ∀ i ∈ range (bands k),
      cut k (i + 1) - cut k i ≤ mesh k)
    (hleft : ∀ᶠ k in l, cut k 0 ≤ -‖a.1‖)
    (hright : ∀ᶠ k in l, ‖a.1‖ < cut k (bands k))
    (hmesh_zero : Tendsto mesh l (nhds 0)) :
    Tendsto
      (fun k ↦ toUltraweak ℂ P (taggedSpectralSum a (cut k) (tag k) (bands k))) l
      (nhds (toUltraweak ℂ P a.1)) := by
  exact (continuous_toUltraweak (𝕜 := ℂ) (M := M) (P := P)).continuousAt.tendsto.comp
    (tendsto_taggedSpectralSum a cut tag bands mesh htag hmesh hleft hright hmesh_zero)

end FilteredFamily

section DyadicConvergence

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] [WStarAlgebra M]

/-- Tagged sums for the canonical dyadic divisions converge in norm whenever every tag lies in its
dyadic band. -/
theorem tendsto_taggedSpectralSum_dyadic
    (a : selfAdjoint M) (tag : ℕ → ℕ → ℝ)
    (htag : ∀ k i, i ∈ range (2 ^ k) →
      dyadicSpectralCut a k i ≤ tag k i ∧
        tag k i ≤ dyadicSpectralCut a k (i + 1)) :
    Tendsto (fun k ↦ taggedSpectralSum a (dyadicSpectralCut a k) (tag k) (2 ^ k))
      atTop (nhds a.1) := by
  apply tendsto_taggedSpectralSum a (dyadicSpectralCut a) tag (fun k ↦ 2 ^ k)
    (dyadicSpectralMesh a)
  · exact Eventually.of_forall fun k i hi ↦ htag k i hi
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
