module

public import LeanOA.Ultraweak.TaggedSpectralSum

@[expose] public section

/-!
# Truncated-affine spectral sums

This file proves that finite spectral sums weighted by `(λ₀ - tag)⁺` approximate the existing
continuous-functional-calculus element `CStarAlgebra.spectralPositivePart a λ₀`.  The main
finite estimate is sharp in the mesh and does not require the cutoff `λ₀` to be a partition
point.  It yields norm convergence along arbitrary mesh-zero filtered families and hence
convergence in every specified ultraweak topology.

The target remains visibly the existing CFC object: by definition,
`CStarAlgebra.spectralPositivePart a r = cfc (fun x : ℝ ↦ (r - x)⁺) a.1`.

No spectral-integral or spectral-resolution structure is introduced.
-/

open Finset Filter
open scoped BigOperators

namespace WStarAlgebra

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] [WStarAlgebra M]

private theorem cut_zero_le_of_adjacent (cut : ℕ → ℝ) (n : ℕ)
    (hcut : ∀ i ∈ range n, cut i ≤ cut (i + 1)) : cut 0 ≤ cut n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    refine (ih fun i hi ↦ hcut i (mem_range.mpr ?_)).trans
      (hcut n (mem_range.mpr (Nat.lt_succ_self n)))
    exact (mem_range.mp hi).trans (Nat.lt_succ_self n)

/-- A tagged sum approximates the compression of `a` to any finite interval of its canonical
spectral family. This version does not require the endpoints to contain the spectrum. -/
theorem norm_taggedSpectralSum_sub_mul_spectralProjectionIio_sub_le
    (a : selfAdjoint M) (cut tag : ℕ → ℝ) (n : ℕ) {δ : ℝ}
    (htag : ∀ i ∈ range n, cut i ≤ tag i ∧ tag i ≤ cut (i + 1))
    (hmesh : ∀ i ∈ range n, cut (i + 1) - cut i ≤ δ)
    (hδ : 0 ≤ δ) :
    ‖taggedSpectralSum a cut tag n -
        a.1 * ((spectralProjectionIio a (cut n)).1 -
          (spectralProjectionIio a (cut 0)).1)‖ ≤ δ := by
  have hcut : ∀ i ∈ range n, cut i ≤ cut (i + 1) :=
    fun i hi ↦ (htag i hi).1.trans (htag i hi).2
  have htagged :=
    lowerSpectralSum_le_taggedSpectralSum_and_taggedSpectralSum_le_upperSpectralSum
      a cut tag n htag
  have ha : lowerSpectralSum a cut n ≤
      a.1 * ((spectralProjectionIio a (cut n)).1 -
        (spectralProjectionIio a (cut 0)).1) ∧
      a.1 * ((spectralProjectionIio a (cut n)).1 -
        (spectralProjectionIio a (cut 0)).1) ≤ upperSpectralSum a cut n :=
    ⟨lowerSpectralSum_le_mul_spectralProjectionIio_sub a cut n hcut,
      mul_spectralProjectionIio_sub_le_upperSpectralSum a cut n hcut⟩
  have hlowerUpper :
      IsSelfAdjoint (lowerSpectralSum a cut n - upperSpectralSum a cut n) :=
    (isSelfAdjoint_lowerSpectralSum a cut n).sub
      (isSelfAdjoint_upperSpectralSum a cut n)
  have hnorm :
      ‖taggedSpectralSum a cut tag n -
          a.1 * ((spectralProjectionIio a (cut n)).1 -
            (spectralProjectionIio a (cut 0)).1)‖ ≤
        ‖upperSpectralSum a cut n - lowerSpectralSum a cut n‖ := by
    calc
      _ ≤ max ‖lowerSpectralSum a cut n - upperSpectralSum a cut n‖
          ‖upperSpectralSum a cut n - lowerSpectralSum a cut n‖ :=
        hlowerUpper.norm_le_max_of_le_of_le
          (sub_le_sub htagged.1 ha.2) (sub_le_sub htagged.2 ha.1)
      _ = ‖upperSpectralSum a cut n - lowerSpectralSum a cut n‖ := by
        rw [norm_sub_rev]
        simp
  refine hnorm.trans ?_
  have hcut0n : cut 0 ≤ cut n := cut_zero_le_of_adjacent cut n hcut
  have hp : IsStarProjection
      ((spectralProjectionIio a (cut n)).1 -
        (spectralProjectionIio a (cut 0)).1) :=
    ((spectralProjectionIio a (cut 0)).2.le_iff_sub
      (spectralProjectionIio a (cut n)).2).mp
      (spectralProjectionIio_mono a hcut0n)
  have hgap_nonneg : 0 ≤ upperSpectralSum a cut n - lowerSpectralSum a cut n :=
    sub_nonneg.mpr
      ((lowerSpectralSum_le_mul_spectralProjectionIio_sub a cut n hcut).trans
        (mul_spectralProjectionIio_sub_le_upperSpectralSum a cut n hcut))
  have hgap_le := upperSpectralSum_sub_lowerSpectralSum_le a cut n hcut hmesh
  calc
    ‖upperSpectralSum a cut n - lowerSpectralSum a cut n‖ ≤
        ‖δ • ((spectralProjectionIio a (cut n)).1 -
          (spectralProjectionIio a (cut 0)).1)‖ :=
      CStarAlgebra.norm_le_norm_of_nonneg_of_le hgap_nonneg hgap_le
    _ = δ * ‖((spectralProjectionIio a (cut n)).1 -
          (spectralProjectionIio a (cut 0)).1)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hδ]
    _ ≤ δ := mul_le_of_le_one_right hδ (IsStarProjection.norm_le _ hp)

private theorem spectralProjectionIio_mul_band_eq_self
    (a : selfAdjoint M) {q s r : ℝ} (hqs : q ≤ s) (hsr : s ≤ r) :
    (spectralProjectionIio a r).1 *
      ((spectralProjectionIio a s).1 - (spectralProjectionIio a q).1) =
        (spectralProjectionIio a s).1 - (spectralProjectionIio a q).1 := by
  let p := spectralProjectionIio a s
  let e := spectralProjectionIio a r
  have hpe : p ≤ e := spectralProjectionIio_mono a hsr
  have hq : spectralProjectionIio a q ≤ p := spectralProjectionIio_mono a hqs
  rw [mul_sub, (p.2.le_iff_mul_eq_right e.2).mp hpe]
  have hqe : spectralProjectionIio a q ≤ e := hq.trans hpe
  rw [((spectralProjectionIio a q).2.le_iff_mul_eq_right e.2).mp hqe]

private theorem spectralProjectionIio_mul_band_eq_zero
    (a : selfAdjoint M) {r q s : ℝ} (hrq : r ≤ q) (hqs : q ≤ s) :
    (spectralProjectionIio a r).1 *
      ((spectralProjectionIio a s).1 - (spectralProjectionIio a q).1) = 0 := by
  have hrs : spectralProjectionIio a r ≤ spectralProjectionIio a s :=
    spectralProjectionIio_mono a (hrq.trans hqs)
  have hrq' : spectralProjectionIio a r ≤ spectralProjectionIio a q :=
    spectralProjectionIio_mono a hrq
  rw [mul_sub,
    ((spectralProjectionIio a r).2.le_iff_mul_eq_left
      (spectralProjectionIio a s).2).mp hrs,
    ((spectralProjectionIio a r).2.le_iff_mul_eq_left
      (spectralProjectionIio a q).2).mp hrq', sub_self]

private theorem spectralPositivePart_mul_band_of_le
    (a : selfAdjoint M) {q s r : ℝ} (hqs : q ≤ s) (hsr : s ≤ r) :
    CStarAlgebra.spectralPositivePart a r *
        ((spectralProjectionIio a s).1 - (spectralProjectionIio a q).1) =
      r • ((spectralProjectionIio a s).1 - (spectralProjectionIio a q).1) -
        a.1 * ((spectralProjectionIio a s).1 - (spectralProjectionIio a q).1) := by
  let p : M := (spectralProjectionIio a s).1 - (spectralProjectionIio a q).1
  calc
    CStarAlgebra.spectralPositivePart a r * p =
        ((algebraMap ℝ M r - a.1) * (spectralProjectionIio a r).1) * p := by
      rw [sub_mul_spectralProjectionIio]
    _ = (algebraMap ℝ M r - a.1) * ((spectralProjectionIio a r).1 * p) := by
      rw [mul_assoc]
    _ = (algebraMap ℝ M r - a.1) * p := by
      rw [spectralProjectionIio_mul_band_eq_self a hqs hsr]
    _ = r • p - a.1 * p := by rw [sub_mul, Algebra.smul_def]

private theorem spectralPositivePart_mul_band_eq_zero
    (a : selfAdjoint M) {r q s : ℝ} (hrq : r ≤ q) (hqs : q ≤ s) :
    CStarAlgebra.spectralPositivePart a r *
        ((spectralProjectionIio a s).1 - (spectralProjectionIio a q).1) = 0 := by
  let p : M := (spectralProjectionIio a s).1 - (spectralProjectionIio a q).1
  calc
    CStarAlgebra.spectralPositivePart a r * p =
        (CStarAlgebra.spectralPositivePart a r * (spectralProjectionIio a r).1) * p := by
      rw [spectralPositivePart_mul_spectralProjectionIio]
    _ = CStarAlgebra.spectralPositivePart a r * ((spectralProjectionIio a r).1 * p) := by
      rw [mul_assoc]
    _ = 0 := by rw [spectralProjectionIio_mul_band_eq_zero a hrq hqs, mul_zero]

/-- The scalar truncated-affine function bounds the compression of the existing spectral positive
part on every canonical spectral band, including a band which contains the cutoff. -/
theorem spectralPositivePart_mul_spectralProjectionIio_sub_bounds
    (a : selfAdjoint M) (r : ℝ) {q s : ℝ} (hqs : q ≤ s) :
    (r - s)⁺ • ((spectralProjectionIio a s).1 - (spectralProjectionIio a q).1) ≤
        CStarAlgebra.spectralPositivePart a r *
          ((spectralProjectionIio a s).1 - (spectralProjectionIio a q).1) ∧
      CStarAlgebra.spectralPositivePart a r *
          ((spectralProjectionIio a s).1 - (spectralProjectionIio a q).1) ≤
        (r - q)⁺ • ((spectralProjectionIio a s).1 - (spectralProjectionIio a q).1) := by
  rcases le_total s r with hsr | hrs
  · rw [spectralPositivePart_mul_band_of_le a hqs hsr,
      _root_.posPart_eq_self.mpr (sub_nonneg.mpr hsr),
      _root_.posPart_eq_self.mpr (sub_nonneg.mpr (hqs.trans hsr))]
    constructor
    · simpa [sub_smul] using sub_le_sub_left
        (spectralProjectionIio_band_bounds a hqs).2
        (r • ((spectralProjectionIio a s).1 - (spectralProjectionIio a q).1))
    · simpa [sub_smul] using sub_le_sub_left
        (spectralProjectionIio_band_bounds a hqs).1
        (r • ((spectralProjectionIio a s).1 - (spectralProjectionIio a q).1))
  · rcases le_total r q with hrq | hqr
    · rw [spectralPositivePart_mul_band_eq_zero a hrq hqs,
        _root_.posPart_eq_zero.mpr (sub_nonpos.mpr (hrq.trans hqs)),
        _root_.posPart_eq_zero.mpr (sub_nonpos.mpr hrq), zero_smul]
      exact ⟨le_rfl, le_rfl⟩
    · let p : M := (spectralProjectionIio a s).1 - (spectralProjectionIio a q).1
      let p0 : M := (spectralProjectionIio a r).1 - (spectralProjectionIio a q).1
      have herp : (spectralProjectionIio a r).1 * p = p0 := by
        dsimp [p, p0]
        rw [mul_sub,
          ((spectralProjectionIio a r).2.le_iff_mul_eq_left
            (spectralProjectionIio a s).2).mp (spectralProjectionIio_mono a hrs),
          ((spectralProjectionIio a q).2.le_iff_mul_eq_right
            (spectralProjectionIio a r).2).mp (spectralProjectionIio_mono a hqr)]
      have hB : CStarAlgebra.spectralPositivePart a r * p = r • p0 - a.1 * p0 := by
        calc
          CStarAlgebra.spectralPositivePart a r * p =
              ((algebraMap ℝ M r - a.1) * (spectralProjectionIio a r).1) * p := by
            rw [sub_mul_spectralProjectionIio]
          _ = (algebraMap ℝ M r - a.1) *
              ((spectralProjectionIio a r).1 * p) := by rw [mul_assoc]
          _ = (algebraMap ℝ M r - a.1) * p0 := by rw [herp]
          _ = r • p0 - a.1 * p0 := by rw [sub_mul, Algebra.smul_def]
      rw [_root_.posPart_eq_zero.mpr (sub_nonpos.mpr hrs), zero_smul, hB,
        _root_.posPart_eq_self.mpr (sub_nonneg.mpr hqr)]
      constructor
      · exact sub_nonneg.mpr (spectralProjectionIio_band_bounds a hqr).2
      · have hpartial := sub_le_sub_left
          (spectralProjectionIio_band_bounds a hqr).1 (r • p0)
        have hp0p : p0 ≤ p := by
          exact sub_le_sub_right
            (show (spectralProjectionIio a r).1 ≤ (spectralProjectionIio a s).1 from
              spectralProjectionIio_mono a hrs)
            (spectralProjectionIio a q).1
        calc
          r • p0 - a.1 * p0 ≤ r • p0 - q • p0 := hpartial
          _ = (r - q) • p0 := by rw [sub_smul]
          _ ≤ (r - q) • p := by
            exact smul_le_smul_of_nonneg_left hp0p (sub_nonneg.mpr hqr)

private theorem posPart_sub_posPart_le_sub {q s r : ℝ} (hqs : q ≤ s) :
    (r - q)⁺ - (r - s)⁺ ≤ s - q := by
  have hmono : (r - s)⁺ ≤ (r - q)⁺ :=
    posPart_mono (sub_le_sub_left hqs r)
  have hlip :=
    (lipschitzWith_posPart : LipschitzWith 1 (posPart : ℝ → ℝ)).dist_le_mul
      (r - q) (r - s)
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul,
    abs_of_nonneg (sub_nonneg.mpr hmono)] at hlip
  have hinput : (r - q) - (r - s) = s - q := by ring
  rw [hinput, abs_of_nonneg (sub_nonneg.mpr hqs)] at hlip
  exact hlip

/-- Endpoint-weighted sums bracket the existing CFC spectral positive part. -/
theorem truncated_affine_endpoint_sums_bound_spectralPositivePart
    (a : selfAdjoint M) (r : ℝ) (cut : ℕ → ℝ) (n : ℕ)
    (hcut : ∀ i ∈ range n, cut i ≤ cut (i + 1))
    (hleft : cut 0 ≤ -‖a.1‖) (hright : ‖a.1‖ < cut n) :
    taggedSpectralSum a cut (fun i ↦ (r - cut (i + 1))⁺) n ≤
        CStarAlgebra.spectralPositivePart a r ∧
      CStarAlgebra.spectralPositivePart a r ≤
        taggedSpectralSum a cut (fun i ↦ (r - cut i)⁺) n := by
  have hsum : ∑ i ∈ range n,
      CStarAlgebra.spectralPositivePart a r *
        ((spectralProjectionIio a (cut (i + 1))).1 -
          (spectralProjectionIio a (cut i)).1) =
      CStarAlgebra.spectralPositivePart a r := by
    rw [← Finset.mul_sum, sum_spectralProjectionIio_sub,
      spectralProjectionIio_sub_eq_one_of_endpoint_bounds a cut n hleft hright, mul_one]
  constructor
  · rw [taggedSpectralSum]
    calc
      _ ≤ ∑ i ∈ range n, CStarAlgebra.spectralPositivePart a r *
          ((spectralProjectionIio a (cut (i + 1))).1 -
            (spectralProjectionIio a (cut i)).1) :=
        Finset.sum_le_sum fun i hi ↦
          (spectralPositivePart_mul_spectralProjectionIio_sub_bounds a r (hcut i hi)).1
      _ = CStarAlgebra.spectralPositivePart a r := hsum
  · rw [taggedSpectralSum]
    calc
      CStarAlgebra.spectralPositivePart a r =
          ∑ i ∈ range n, CStarAlgebra.spectralPositivePart a r *
            ((spectralProjectionIio a (cut (i + 1))).1 -
              (spectralProjectionIio a (cut i)).1) := hsum.symm
      _ ≤ _ := Finset.sum_le_sum fun i hi ↦
        (spectralPositivePart_mul_spectralProjectionIio_sub_bounds a r (hcut i hi)).2

/-- Applying the truncated-affine weight to an arbitrary tag stays between its two endpoint
versions. -/
theorem truncated_affine_endpoint_sums_bound_taggedSpectralSum
    (a : selfAdjoint M) (r : ℝ) (cut tag : ℕ → ℝ) (n : ℕ)
    (htag : ∀ i ∈ range n, cut i ≤ tag i ∧ tag i ≤ cut (i + 1)) :
    taggedSpectralSum a cut (fun i ↦ (r - cut (i + 1))⁺) n ≤
        taggedSpectralSum a cut (fun i ↦ (r - tag i)⁺) n ∧
      taggedSpectralSum a cut (fun i ↦ (r - tag i)⁺) n ≤
        taggedSpectralSum a cut (fun i ↦ (r - cut i)⁺) n := by
  rw [taggedSpectralSum, taggedSpectralSum, taggedSpectralSum]
  constructor
  · exact Finset.sum_le_sum fun i hi ↦
      smul_le_smul_of_nonneg_right
        (posPart_mono (sub_le_sub_left (htag i hi).2 r))
        (sub_nonneg.mpr (spectralProjectionIio_mono a
          ((htag i hi).1.trans (htag i hi).2)))
  · exact Finset.sum_le_sum fun i hi ↦
      smul_le_smul_of_nonneg_right
        (posPart_mono (sub_le_sub_left (htag i hi).1 r))
        (sub_nonneg.mpr (spectralProjectionIio_mono a
          ((htag i hi).1.trans (htag i hi).2)))

/-- The gap between the two truncated-affine endpoint sums is bounded above by the ordinary
upper/lower spectral-sum gap. -/
theorem truncated_affine_endpoint_sum_gap_le
    (a : selfAdjoint M) (r : ℝ) (cut : ℕ → ℝ) (n : ℕ)
    (hcut : ∀ i ∈ range n, cut i ≤ cut (i + 1)) :
    taggedSpectralSum a cut (fun i ↦ (r - cut i)⁺) n -
        taggedSpectralSum a cut (fun i ↦ (r - cut (i + 1))⁺) n ≤
      upperSpectralSum a cut n - lowerSpectralSum a cut n := by
  rw [taggedSpectralSum, taggedSpectralSum, upperSpectralSum_sub_lowerSpectralSum,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum fun i hi ↦ by
    rw [← sub_smul]
    exact smul_le_smul_of_nonneg_right
      ((posPart_sub_posPart_le_sub (hcut i hi)).trans le_rfl)
      (sub_nonneg.mpr (spectralProjectionIio_mono a (hcut i hi)))

/-- A truncated-affine weighted tagged sum approximates the existing CFC spectral positive part
with norm error no larger than the mesh. The cutoff need not be a partition point. -/
theorem norm_truncated_affine_taggedSpectralSum_sub_spectralPositivePart_le
    (a : selfAdjoint M) (r : ℝ) (cut tag : ℕ → ℝ) (n : ℕ) {δ : ℝ}
    (htag : ∀ i ∈ range n, cut i ≤ tag i ∧ tag i ≤ cut (i + 1))
    (hmesh : ∀ i ∈ range n, cut (i + 1) - cut i ≤ δ)
    (hleft : cut 0 ≤ -‖a.1‖) (hright : ‖a.1‖ < cut n) :
    ‖taggedSpectralSum a cut (fun i ↦ (r - tag i)⁺) n -
      CStarAlgebra.spectralPositivePart a r‖ ≤ δ := by
  let lower := taggedSpectralSum a cut (fun i ↦ (r - cut (i + 1))⁺) n
  let upper := taggedSpectralSum a cut (fun i ↦ (r - cut i)⁺) n
  let tagged := taggedSpectralSum a cut (fun i ↦ (r - tag i)⁺) n
  let target := CStarAlgebra.spectralPositivePart a r
  have hcut : ∀ i ∈ range n, cut i ≤ cut (i + 1) :=
    fun i hi ↦ (htag i hi).1.trans (htag i hi).2
  have htarget := truncated_affine_endpoint_sums_bound_spectralPositivePart
    a r cut n hcut hleft hright
  have htagged := truncated_affine_endpoint_sums_bound_taggedSpectralSum
    a r cut tag n htag
  have hlowerUpper : IsSelfAdjoint (lower - upper) :=
    (isSelfAdjoint_taggedSpectralSum a cut (fun i ↦ (r - cut (i + 1))⁺) n).sub
      (isSelfAdjoint_taggedSpectralSum a cut (fun i ↦ (r - cut i)⁺) n)
  have hnorm : ‖tagged - target‖ ≤ ‖upper - lower‖ := by
    calc
      _ ≤ max ‖lower - upper‖ ‖upper - lower‖ :=
        hlowerUpper.norm_le_max_of_le_of_le
          (sub_le_sub htagged.1 htarget.2) (sub_le_sub htagged.2 htarget.1)
      _ = ‖upper - lower‖ := by rw [norm_sub_rev]; simp
  refine hnorm.trans ?_
  have hgap_nonneg : 0 ≤ upper - lower := sub_nonneg.mpr
    (truncated_affine_endpoint_sums_bound_taggedSpectralSum
      a r cut cut n (fun i hi ↦ ⟨le_rfl, hcut i hi⟩)).1
  have hgap_le : upper - lower ≤ upperSpectralSum a cut n - lowerSpectralSum a cut n :=
    truncated_affine_endpoint_sum_gap_le a r cut n hcut
  calc
    ‖upper - lower‖ ≤ ‖upperSpectralSum a cut n - lowerSpectralSum a cut n‖ :=
      CStarAlgebra.norm_le_norm_of_nonneg_of_le hgap_nonneg hgap_le
    _ ≤ δ := norm_upperSpectralSum_sub_lowerSpectralSum_le
      a cut n hcut hmesh hleft hright

/-- Truncated-affine weighted tagged sums converge in norm to the existing CFC spectral positive
part along every mesh-zero filtered family. -/
theorem tendsto_truncated_affine_taggedSpectralSum
    {I : Type*} {l : Filter I} (a : selfAdjoint M) (r : ℝ)
    (cut tag : I → ℕ → ℝ) (bands : I → ℕ) (mesh : I → ℝ)
    (htag : ∀ᶠ k in l, ∀ i ∈ range (bands k),
      cut k i ≤ tag k i ∧ tag k i ≤ cut k (i + 1))
    (hmesh : ∀ᶠ k in l, ∀ i ∈ range (bands k),
      cut k (i + 1) - cut k i ≤ mesh k)
    (hleft : ∀ᶠ k in l, cut k 0 ≤ -‖a.1‖)
    (hright : ∀ᶠ k in l, ‖a.1‖ < cut k (bands k))
    (hmesh_zero : Tendsto mesh l (nhds 0)) :
    Tendsto
      (fun k ↦ taggedSpectralSum a (cut k) (fun i ↦ (r - tag k i)⁺) (bands k)) l
      (nhds (CStarAlgebra.spectralPositivePart a r)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hmesh_zero
  filter_upwards [htag, hmesh, hleft, hright] with k htk hmk hl hr
  exact norm_truncated_affine_taggedSpectralSum_sub_spectralPositivePart_le
    a r (cut k) (tag k) (bands k) htk hmk hl hr

/-- The same filtered convergence holds in every specified ultraweak topology. -/
theorem tendsto_truncated_affine_taggedSpectralSum_ultraweak
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] [Predual ℂ M P]
    {I : Type*} {l : Filter I} (a : selfAdjoint M) (r : ℝ)
    (cut tag : I → ℕ → ℝ) (bands : I → ℕ) (mesh : I → ℝ)
    (htag : ∀ᶠ k in l, ∀ i ∈ range (bands k),
      cut k i ≤ tag k i ∧ tag k i ≤ cut k (i + 1))
    (hmesh : ∀ᶠ k in l, ∀ i ∈ range (bands k),
      cut k (i + 1) - cut k i ≤ mesh k)
    (hleft : ∀ᶠ k in l, cut k 0 ≤ -‖a.1‖)
    (hright : ∀ᶠ k in l, ‖a.1‖ < cut k (bands k))
    (hmesh_zero : Tendsto mesh l (nhds 0)) :
    Tendsto
      (fun k ↦ toUltraweak ℂ P
        (taggedSpectralSum a (cut k) (fun i ↦ (r - tag k i)⁺) (bands k))) l
      (nhds (toUltraweak ℂ P (CStarAlgebra.spectralPositivePart a r))) := by
  exact (continuous_toUltraweak (𝕜 := ℂ) (M := M) (P := P)).continuousAt.tendsto.comp
    (tendsto_truncated_affine_taggedSpectralSum
      a r cut tag bands mesh htag hmesh hleft hright hmesh_zero)

/-- Truncated-affine weighted sums over the existing dyadic divisions converge in norm for every
choice of in-band tags. -/
theorem tendsto_truncated_affine_taggedSpectralSum_dyadic
    (a : selfAdjoint M) (r : ℝ) (tag : ℕ → ℕ → ℝ)
    (htag : ∀ k i, i ∈ range (2 ^ k) →
      dyadicSpectralCut a k i ≤ tag k i ∧
        tag k i ≤ dyadicSpectralCut a k (i + 1)) :
    Tendsto
      (fun k ↦ taggedSpectralSum a (dyadicSpectralCut a k)
        (fun i ↦ (r - tag k i)⁺) (2 ^ k)) atTop
      (nhds (CStarAlgebra.spectralPositivePart a r)) := by
  apply tendsto_truncated_affine_taggedSpectralSum a r
    (dyadicSpectralCut a) tag (fun k ↦ 2 ^ k) (dyadicSpectralMesh a)
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

end WStarAlgebra
