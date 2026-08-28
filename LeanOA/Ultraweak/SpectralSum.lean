module

public import LeanOA.Ultraweak.SpectralProjection

@[expose] public section

/-!
# Finite sums for a spectral resolution

This file defines the lower and upper finite sums associated to the lower spectral projections of
a self-adjoint element.  It proves the finite-partition estimate in the existence part of Sakai,
Theorem 1.11.3: when the cuts extend beyond the norm bounds, the two sums bracket the element and
their difference is bounded by the mesh times the identity.

The interface uses a function `cut : ℕ → ℝ` and the first `n` adjacent intervals.  It does not
introduce a repository-specific partition structure; the proof reuses Mathlib's telescoping
finite-sum identity and the spectral-band estimate already established in
`LeanOA.Ultraweak.SpectralProjection`.
-/

open Finset
open scoped BigOperators

namespace WStarAlgebra

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] [WStarAlgebra M]

/-- The lower finite sum for the first `n` bands of a spectral family. -/
noncomputable def lowerSpectralSum (a : selfAdjoint M) (cut : ℕ → ℝ) (n : ℕ) : M :=
  ∑ i ∈ range n,
    cut i • ((spectralProjectionIio a (cut (i + 1))).1 -
      (spectralProjectionIio a (cut i)).1)

/-- The upper finite sum for the first `n` bands of a spectral family. -/
noncomputable def upperSpectralSum (a : selfAdjoint M) (cut : ℕ → ℝ) (n : ℕ) : M :=
  ∑ i ∈ range n,
    cut (i + 1) • ((spectralProjectionIio a (cut (i + 1))).1 -
      (spectralProjectionIio a (cut i)).1)

/-- Every lower spectral sum is self-adjoint. -/
theorem isSelfAdjoint_lowerSpectralSum (a : selfAdjoint M) (cut : ℕ → ℝ) (n : ℕ) :
    IsSelfAdjoint (lowerSpectralSum a cut n) := by
  rw [lowerSpectralSum]
  apply isSelfAdjoint_sum
  intro i hi
  exact (isSelfAdjoint_iff.mpr (star_trivial (cut i))).smul
    ((spectralProjectionIio a (cut (i + 1))).2.isSelfAdjoint.sub
      (spectralProjectionIio a (cut i)).2.isSelfAdjoint)

/-- Every upper spectral sum is self-adjoint. -/
theorem isSelfAdjoint_upperSpectralSum (a : selfAdjoint M) (cut : ℕ → ℝ) (n : ℕ) :
    IsSelfAdjoint (upperSpectralSum a cut n) := by
  rw [upperSpectralSum]
  apply isSelfAdjoint_sum
  intro i hi
  exact (isSelfAdjoint_iff.mpr (star_trivial (cut (i + 1)))).smul
    ((spectralProjectionIio a (cut (i + 1))).2.isSelfAdjoint.sub
      (spectralProjectionIio a (cut i)).2.isSelfAdjoint)

/-- The sum of adjacent spectral-band projections telescopes to the difference of the endpoint
projections. -/
theorem sum_spectralProjectionIio_sub (a : selfAdjoint M) (cut : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ range n,
        ((spectralProjectionIio a (cut (i + 1))).1 -
          (spectralProjectionIio a (cut i)).1) =
      (spectralProjectionIio a (cut n)).1 - (spectralProjectionIio a (cut 0)).1 := by
  exact Finset.sum_range_sub (fun i ↦ (spectralProjectionIio a (cut i)).1) n

/-- The lower spectral sum is bounded by the self-adjoint element restricted to the union of the
chosen spectral bands. -/
theorem lowerSpectralSum_le_mul_spectralProjectionIio_sub
    (a : selfAdjoint M) (cut : ℕ → ℝ) (n : ℕ)
    (hcut : ∀ i ∈ range n, cut i ≤ cut (i + 1)) :
    lowerSpectralSum a cut n ≤
      a.1 * ((spectralProjectionIio a (cut n)).1 -
        (spectralProjectionIio a (cut 0)).1) := by
  rw [lowerSpectralSum, ← sum_spectralProjectionIio_sub a cut n, mul_sum]
  exact Finset.sum_le_sum fun i hi ↦ (spectralProjectionIio_band_bounds a (hcut i hi)).1

/-- The self-adjoint element restricted to the union of the chosen spectral bands is bounded by
the upper spectral sum. -/
theorem mul_spectralProjectionIio_sub_le_upperSpectralSum
    (a : selfAdjoint M) (cut : ℕ → ℝ) (n : ℕ)
    (hcut : ∀ i ∈ range n, cut i ≤ cut (i + 1)) :
    a.1 * ((spectralProjectionIio a (cut n)).1 -
        (spectralProjectionIio a (cut 0)).1) ≤
      upperSpectralSum a cut n := by
  rw [upperSpectralSum, ← sum_spectralProjectionIio_sub a cut n, mul_sum]
  exact Finset.sum_le_sum fun i hi ↦ (spectralProjectionIio_band_bounds a (hcut i hi)).2

/-- The difference of the upper and lower spectral sums is the sum of the spectral bands weighted
by their widths. -/
theorem upperSpectralSum_sub_lowerSpectralSum
    (a : selfAdjoint M) (cut : ℕ → ℝ) (n : ℕ) :
    upperSpectralSum a cut n - lowerSpectralSum a cut n =
      ∑ i ∈ range n, (cut (i + 1) - cut i) •
        ((spectralProjectionIio a (cut (i + 1))).1 -
          (spectralProjectionIio a (cut i)).1) := by
  rw [upperSpectralSum, lowerSpectralSum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [sub_smul]

/-- If every selected interval has width at most `δ`, the spectral-sum gap is at most `δ` times
the difference of the endpoint projections. -/
theorem upperSpectralSum_sub_lowerSpectralSum_le
    (a : selfAdjoint M) (cut : ℕ → ℝ) (n : ℕ) {δ : ℝ}
    (hcut : ∀ i ∈ range n, cut i ≤ cut (i + 1))
    (hmesh : ∀ i ∈ range n, cut (i + 1) - cut i ≤ δ) :
    upperSpectralSum a cut n - lowerSpectralSum a cut n ≤
      δ • ((spectralProjectionIio a (cut n)).1 -
        (spectralProjectionIio a (cut 0)).1) := by
  rw [upperSpectralSum_sub_lowerSpectralSum, ← sum_spectralProjectionIio_sub a cut n,
    Finset.smul_sum]
  exact Finset.sum_le_sum fun i hi ↦
    smul_le_smul_of_nonneg_right (hmesh i hi)
      (sub_nonneg.mpr (spectralProjectionIio_mono a (hcut i hi)))

/-- Cuts extending past both norm bounds exhaust the identity projection. -/
theorem spectralProjectionIio_sub_eq_one_of_endpoint_bounds
    (a : selfAdjoint M) (cut : ℕ → ℝ) (n : ℕ)
    (hleft : cut 0 ≤ -‖a.1‖) (hright : ‖a.1‖ < cut n) :
    (spectralProjectionIio a (cut n)).1 -
        (spectralProjectionIio a (cut 0)).1 = 1 := by
  rw [spectralProjectionIio_eq_zero_of_le_neg_norm a hleft,
    spectralProjectionIio_eq_one_of_norm_lt a hright, Subtype.coe_mk,
    Subtype.coe_mk, sub_zero]

/-- A lower spectral sum whose endpoint cuts lie beyond the norm bounds is below the original
self-adjoint element. -/
theorem lowerSpectralSum_le_self
    (a : selfAdjoint M) (cut : ℕ → ℝ) (n : ℕ)
    (hcut : ∀ i ∈ range n, cut i ≤ cut (i + 1))
    (hleft : cut 0 ≤ -‖a.1‖) (hright : ‖a.1‖ < cut n) :
    lowerSpectralSum a cut n ≤ a.1 := by
  calc
    lowerSpectralSum a cut n ≤
        a.1 * ((spectralProjectionIio a (cut n)).1 -
          (spectralProjectionIio a (cut 0)).1) :=
      lowerSpectralSum_le_mul_spectralProjectionIio_sub a cut n hcut
    _ = a.1 := by
      rw [spectralProjectionIio_sub_eq_one_of_endpoint_bounds a cut n hleft hright, mul_one]

/-- An upper spectral sum whose endpoint cuts lie beyond the norm bounds is above the original
self-adjoint element. -/
theorem self_le_upperSpectralSum
    (a : selfAdjoint M) (cut : ℕ → ℝ) (n : ℕ)
    (hcut : ∀ i ∈ range n, cut i ≤ cut (i + 1))
    (hleft : cut 0 ≤ -‖a.1‖) (hright : ‖a.1‖ < cut n) :
    a.1 ≤ upperSpectralSum a cut n := by
  calc
    a.1 = a.1 * ((spectralProjectionIio a (cut n)).1 -
          (spectralProjectionIio a (cut 0)).1) := by
      rw [spectralProjectionIio_sub_eq_one_of_endpoint_bounds a cut n hleft hright, mul_one]
    _ ≤ upperSpectralSum a cut n :=
      mul_spectralProjectionIio_sub_le_upperSpectralSum a cut n hcut

/-- The lower and upper finite spectral sums bracket the original self-adjoint element. -/
theorem lowerSpectralSum_le_self_and_self_le_upperSpectralSum
    (a : selfAdjoint M) (cut : ℕ → ℝ) (n : ℕ)
    (hcut : ∀ i ∈ range n, cut i ≤ cut (i + 1))
    (hleft : cut 0 ≤ -‖a.1‖) (hright : ‖a.1‖ < cut n) :
    lowerSpectralSum a cut n ≤ a.1 ∧ a.1 ≤ upperSpectralSum a cut n :=
  ⟨lowerSpectralSum_le_self a cut n hcut hleft hright,
    self_le_upperSpectralSum a cut n hcut hleft hright⟩

/-- Under the endpoint hypotheses, a mesh bound gives the order estimate
`upperSpectralSum - lowerSpectralSum ≤ δ • 1`. -/
theorem upperSpectralSum_sub_lowerSpectralSum_le_smul_one
    (a : selfAdjoint M) (cut : ℕ → ℝ) (n : ℕ) {δ : ℝ}
    (hcut : ∀ i ∈ range n, cut i ≤ cut (i + 1))
    (hmesh : ∀ i ∈ range n, cut (i + 1) - cut i ≤ δ)
    (hleft : cut 0 ≤ -‖a.1‖) (hright : ‖a.1‖ < cut n) :
    upperSpectralSum a cut n - lowerSpectralSum a cut n ≤ δ • (1 : M) := by
  rw [← spectralProjectionIio_sub_eq_one_of_endpoint_bounds a cut n hleft hright]
  exact upperSpectralSum_sub_lowerSpectralSum_le a cut n hcut hmesh

/-- **Finite-partition estimate in Sakai, Theorem 1.11.3.**  The norm gap between the upper and
lower spectral sums is at most the mesh. -/
theorem norm_upperSpectralSum_sub_lowerSpectralSum_le
    (a : selfAdjoint M) (cut : ℕ → ℝ) (n : ℕ) {δ : ℝ}
    (hcut : ∀ i ∈ range n, cut i ≤ cut (i + 1))
    (hmesh : ∀ i ∈ range n, cut (i + 1) - cut i ≤ δ)
    (hleft : cut 0 ≤ -‖a.1‖) (hright : ‖a.1‖ < cut n) :
    ‖upperSpectralSum a cut n - lowerSpectralSum a cut n‖ ≤ δ := by
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    linarith [norm_nonneg a.1]
  have hzero : 0 ∈ range n := Finset.mem_range.mpr hn
  have hδ : 0 ≤ δ :=
    (sub_nonneg.mpr (hcut 0 hzero)).trans (hmesh 0 hzero)
  have hbounds :=
    lowerSpectralSum_le_self_and_self_le_upperSpectralSum a cut n hcut hleft hright
  have hgap_nonneg : 0 ≤ upperSpectralSum a cut n - lowerSpectralSum a cut n :=
    sub_nonneg.mpr (hbounds.1.trans hbounds.2)
  have hgap_le :=
    upperSpectralSum_sub_lowerSpectralSum_le_smul_one a cut n hcut hmesh hleft hright
  calc
    ‖upperSpectralSum a cut n - lowerSpectralSum a cut n‖ ≤ ‖δ • (1 : M)‖ :=
      CStarAlgebra.norm_le_norm_of_nonneg_of_le hgap_nonneg hgap_le
    _ = δ * ‖(1 : M)‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hδ]
    _ ≤ δ := mul_le_of_le_one_right hδ
      (IsStarProjection.norm_le (1 : M) (IsStarProjection.one M))

/-- The lower spectral sum approximates the self-adjoint element with error at most the mesh. -/
theorem norm_self_sub_lowerSpectralSum_le
    (a : selfAdjoint M) (cut : ℕ → ℝ) (n : ℕ) {δ : ℝ}
    (hcut : ∀ i ∈ range n, cut i ≤ cut (i + 1))
    (hmesh : ∀ i ∈ range n, cut (i + 1) - cut i ≤ δ)
    (hleft : cut 0 ≤ -‖a.1‖) (hright : ‖a.1‖ < cut n) :
    ‖a.1 - lowerSpectralSum a cut n‖ ≤ δ := by
  have hbounds :=
    lowerSpectralSum_le_self_and_self_le_upperSpectralSum a cut n hcut hleft hright
  calc
    ‖a.1 - lowerSpectralSum a cut n‖ ≤
        ‖upperSpectralSum a cut n - lowerSpectralSum a cut n‖ :=
      CStarAlgebra.norm_le_norm_of_nonneg_of_le (sub_nonneg.mpr hbounds.1)
        (sub_le_sub_right hbounds.2 _)
    _ ≤ δ :=
      norm_upperSpectralSum_sub_lowerSpectralSum_le a cut n hcut hmesh hleft hright

/-- The upper spectral sum approximates the self-adjoint element with error at most the mesh. -/
theorem norm_upperSpectralSum_sub_self_le
    (a : selfAdjoint M) (cut : ℕ → ℝ) (n : ℕ) {δ : ℝ}
    (hcut : ∀ i ∈ range n, cut i ≤ cut (i + 1))
    (hmesh : ∀ i ∈ range n, cut (i + 1) - cut i ≤ δ)
    (hleft : cut 0 ≤ -‖a.1‖) (hright : ‖a.1‖ < cut n) :
    ‖upperSpectralSum a cut n - a.1‖ ≤ δ := by
  have hbounds :=
    lowerSpectralSum_le_self_and_self_le_upperSpectralSum a cut n hcut hleft hright
  calc
    ‖upperSpectralSum a cut n - a.1‖ ≤
        ‖upperSpectralSum a cut n - lowerSpectralSum a cut n‖ :=
      CStarAlgebra.norm_le_norm_of_nonneg_of_le (sub_nonneg.mpr hbounds.2)
        (sub_le_sub_left hbounds.1 _)
    _ ≤ δ :=
      norm_upperSpectralSum_sub_lowerSpectralSum_le a cut n hcut hmesh hleft hright

end WStarAlgebra
