module

public import LeanOA.Mathlib.Analysis.CStarAlgebra.Projection

@[expose] public section

/-!
# Scratch finite decomposition for Sakai 1.11.3 uniqueness

This file tests only the finite algebra behind inserting a cutoff into a division for an explicit
monotone family of star projections.  It deliberately introduces no public spectral-family,
resolution, PVM, or integral structure.

If a future PVM `E` induces `e r = E (Set.Iio r)`, then `band e q s = e s - e q` represents
`E (Set.Ico q s)`: the left endpoint is included and the right endpoint is excluded.  Thus the
cutoff atom belongs to the band *above* the inserted cutoff.
-/

open Finset
open scoped BigOperators

namespace Scratch.SakaiUniquenessFinite

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

abbrev StarProjection (A : Type*) [Mul A] [Star A] := {p : A // IsStarProjection p}

/-- The projection increment associated with the half-open band `[q, s)`. -/
def band (e : ℝ → StarProjection A) (q s : ℝ) : A :=
  (e s).1 - (e q).1

/-- Monotonicity makes every ordered band a star projection. -/
theorem isStarProjection_band (e : ℝ → StarProjection A) (he : Monotone e)
    {q s : ℝ} (hqs : q ≤ s) : IsStarProjection (band e q s) := by
  exact ((e q).2.le_iff_sub (e s).2).mp (he hqs)

omit [PartialOrder A] [StarOrderedRing A] in
/-- Inserting `r` splits `[q,s)` as `[q,r)` plus `[r,s)`. -/
theorem band_add_band (e : ℝ → StarProjection A) (q r s : ℝ) :
    band e q r + band e r s = band e q s := by
  simp only [band]
  noncomm_ring

/-- A lower projection acts as the identity from the left on every band lying below its cut. -/
theorem mul_band_eq_self_of_le (e : ℝ → StarProjection A) (he : Monotone e)
    {q s r : ℝ} (hqs : q ≤ s) (hsr : s ≤ r) :
    (e r).1 * band e q s = band e q s := by
  rw [band, mul_sub,
    ((e s).2.le_iff_mul_eq_right (e r).2).mp (he hsr),
    ((e q).2.le_iff_mul_eq_right (e r).2).mp (he (hqs.trans hsr))]

/-- A lower projection acts as the identity from the right on every band lying below its cut. -/
theorem band_mul_eq_self_of_le (e : ℝ → StarProjection A) (he : Monotone e)
    {q s r : ℝ} (hqs : q ≤ s) (hsr : s ≤ r) :
    band e q s * (e r).1 = band e q s := by
  rw [band, sub_mul,
    ((e s).2.le_iff_mul_eq_left (e r).2).mp (he hsr),
    ((e q).2.le_iff_mul_eq_left (e r).2).mp (he (hqs.trans hsr))]

/-- A lower projection kills from the left every band starting at or above its cut. -/
theorem mul_band_eq_zero_of_le (e : ℝ → StarProjection A) (he : Monotone e)
    {r q s : ℝ} (hrq : r ≤ q) (hqs : q ≤ s) :
    (e r).1 * band e q s = 0 := by
  rw [band, mul_sub,
    ((e r).2.le_iff_mul_eq_left (e s).2).mp (he (hrq.trans hqs)),
    ((e r).2.le_iff_mul_eq_left (e q).2).mp (he hrq), sub_self]

/-- A lower projection kills from the right every band starting at or above its cut. -/
theorem band_mul_eq_zero_of_le (e : ℝ → StarProjection A) (he : Monotone e)
    {r q s : ℝ} (hrq : r ≤ q) (hqs : q ≤ s) :
    band e q s * (e r).1 = 0 := by
  rw [band, sub_mul,
    ((e r).2.le_iff_mul_eq_right (e s).2).mp (he (hrq.trans hqs)),
    ((e r).2.le_iff_mul_eq_right (e q).2).mp (he hrq), sub_self]

/-- Multiplication by the inserted cutoff extracts `[q,r)` from a crossing band `[q,s)`. -/
theorem mul_band_eq_lower_band (e : ℝ → StarProjection A) (he : Monotone e)
    {q r s : ℝ} (hqr : q ≤ r) (hrs : r ≤ s) :
    (e r).1 * band e q s = band e q r := by
  rw [band, band, mul_sub,
    ((e r).2.le_iff_mul_eq_left (e s).2).mp (he hrs),
    ((e q).2.le_iff_mul_eq_right (e r).2).mp (he hqr)]

/-- The right-handed crossing-band identity. -/
theorem band_mul_eq_lower_band (e : ℝ → StarProjection A) (he : Monotone e)
    {q r s : ℝ} (hqr : q ≤ r) (hrs : r ≤ s) :
    band e q s * (e r).1 = band e q r := by
  rw [band, band, sub_mul,
    ((e r).2.le_iff_mul_eq_right (e s).2).mp (he hrs),
    ((e q).2.le_iff_mul_eq_left (e r).2).mp (he hqr)]

/-- The two bands created by an inserted cutoff are orthogonal in the displayed order. -/
theorem lower_band_mul_upper_band_eq_zero (e : ℝ → StarProjection A)
    (he : Monotone e) {q r s : ℝ} (hqr : q ≤ r) (hrs : r ≤ s) :
    band e q r * band e r s = 0 := by
  exact (e q).2.sub_mul_sub_eq_zero_of_le (e r).2 (e r).2 (e s).2
    (he hqr) le_rfl (he hrs)

/-- Orthogonality also holds in the reverse order. -/
theorem upper_band_mul_lower_band_eq_zero (e : ℝ → StarProjection A)
    (he : Monotone e) {q r s : ℝ} (hqr : q ≤ r) (hrs : r ≤ s) :
    band e r s * band e q r = 0 := by
  have h := congr_arg star (lower_band_mul_upper_band_eq_zero e he hqr hrs)
  simpa only [star_mul, star_zero,
    (isStarProjection_band e he hqr).isSelfAdjoint.star_eq,
    (isStarProjection_band e he hrs).isSelfAdjoint.star_eq] using h

/-- Insert `r` immediately after the cut numbered `j`. -/
def insertCut (cut : ℕ → ℝ) (j : ℕ) (r : ℝ) (i : ℕ) : ℝ :=
  if i ≤ j then cut i else if i = j + 1 then r else cut (i - 1)

@[simp]
theorem insertCut_of_le (cut : ℕ → ℝ) (j : ℕ) (r : ℝ) {i : ℕ} (hi : i ≤ j) :
    insertCut cut j r i = cut i := by
  simp [insertCut, hi]

@[simp]
theorem insertCut_succ (cut : ℕ → ℝ) (j : ℕ) (r : ℝ) :
    insertCut cut j r (j + 1) = r := by
  simp [insertCut]

@[simp]
theorem insertCut_succ_succ (cut : ℕ → ℝ) (j k : ℕ) (r : ℝ) :
    insertCut cut j r (j + 2 + k) = cut (j + 1 + k) := by
  simp only [insertCut]
  split
  · omega
  split
  · omega
  · congr 1
    omega

omit [PartialOrder A] [StarOrderedRing A] in
/-- The old crossing band is exactly the sum of the two new bands after insertion. -/
theorem band_at_insertCut_add_succ (e : ℝ → StarProjection A)
    (cut : ℕ → ℝ) (j : ℕ) (r : ℝ) :
    band e (insertCut cut j r j) (insertCut cut j r (j + 1)) +
        band e (insertCut cut j r (j + 1)) (insertCut cut j r (j + 2)) =
      band e (cut j) (cut (j + 1)) := by
  rw [insertCut_of_le cut j r le_rfl, insertCut_succ,
    show j + 2 = j + 2 + 0 by omega, insertCut_succ_succ]
  simpa using band_add_band e (cut j) r (cut (j + 1))

omit [PartialOrder A] [StarOrderedRing A] in
/-- The complete unweighted band sum is unchanged by inserting a cutoff into a finite division. -/
theorem sum_band_insertCut (e : ℝ → StarProjection A) (cut : ℕ → ℝ)
    {j n : ℕ} (hjn : j < n) (r : ℝ) :
    ∑ i ∈ range (n + 1),
        band e (insertCut cut j r i) (insertCut cut j r (i + 1)) =
      ∑ i ∈ range n, band e (cut i) (cut (i + 1)) := by
  have hn : n + 1 = j + 2 + (n - j - 1) := by omega
  have hj1 : j + 1 ≤ n := Nat.succ_le_iff.mpr hjn
  have htail : j + 1 + (n - j - 1) = n := by
    rw [Nat.sub_sub, Nat.add_sub_of_le hj1]
  calc
    ∑ i ∈ range (n + 1),
        band e (insertCut cut j r i) (insertCut cut j r (i + 1)) =
        (e (insertCut cut j r (n + 1))).1 - (e (insertCut cut j r 0)).1 := by
      simpa only [band] using
        (Finset.sum_range_sub (fun i ↦ (e (insertCut cut j r i)).1) (n + 1))
    _ = (e (cut n)).1 - (e (cut 0)).1 := by
      rw [insertCut_of_le cut j r (Nat.zero_le j), hn, insertCut_succ_succ]
      rw [htail]
    _ = ∑ i ∈ range n, band e (cut i) (cut (i + 1)) := by
      simpa only [band] using
        (Finset.sum_range_sub (fun i ↦ (e (cut i)).1) n).symm

/-- A fixed lower projection acts as the identity on a finite weighted sum of bands below it. -/
theorem mul_weightedBandSum_eq_self_of_below (e : ℝ → StarProjection A)
    (he : Monotone e) (r : ℝ) (cut weight : ℕ → ℝ) (n : ℕ)
    (hcut : ∀ i ∈ range n, cut i ≤ cut (i + 1))
    (hbelow : ∀ i ∈ range n, cut (i + 1) ≤ r) :
    (e r).1 * ∑ i ∈ range n, weight i • band e (cut i) (cut (i + 1)) =
      ∑ i ∈ range n, weight i • band e (cut i) (cut (i + 1)) := by
  rw [mul_sum]
  apply sum_congr rfl
  intro i hi
  rw [mul_smul_comm, mul_band_eq_self_of_le e he (hcut i hi) (hbelow i hi)]

/-- Right multiplication gives the same finite below-cut identity. -/
theorem weightedBandSum_mul_eq_self_of_below (e : ℝ → StarProjection A)
    (he : Monotone e) (r : ℝ) (cut weight : ℕ → ℝ) (n : ℕ)
    (hcut : ∀ i ∈ range n, cut i ≤ cut (i + 1))
    (hbelow : ∀ i ∈ range n, cut (i + 1) ≤ r) :
    (∑ i ∈ range n, weight i • band e (cut i) (cut (i + 1))) * (e r).1 =
      ∑ i ∈ range n, weight i • band e (cut i) (cut (i + 1)) := by
  rw [sum_mul]
  apply sum_congr rfl
  intro i hi
  rw [smul_mul_assoc, band_mul_eq_self_of_le e he (hcut i hi) (hbelow i hi)]

/-- A fixed lower projection kills a finite weighted sum of bands at or above its cut. -/
theorem mul_weightedBandSum_eq_zero_of_above (e : ℝ → StarProjection A)
    (he : Monotone e) (r : ℝ) (cut weight : ℕ → ℝ) (n : ℕ)
    (hcut : ∀ i ∈ range n, cut i ≤ cut (i + 1))
    (habove : ∀ i ∈ range n, r ≤ cut i) :
    (e r).1 * ∑ i ∈ range n, weight i • band e (cut i) (cut (i + 1)) = 0 := by
  rw [mul_sum]
  apply sum_eq_zero
  intro i hi
  rw [mul_smul_comm, mul_band_eq_zero_of_le e he (habove i hi) (hcut i hi), smul_zero]

/-- Right multiplication gives the same finite above-cut annihilation identity. -/
theorem weightedBandSum_mul_eq_zero_of_above (e : ℝ → StarProjection A)
    (he : Monotone e) (r : ℝ) (cut weight : ℕ → ℝ) (n : ℕ)
    (hcut : ∀ i ∈ range n, cut i ≤ cut (i + 1))
    (habove : ∀ i ∈ range n, r ≤ cut i) :
    (∑ i ∈ range n, weight i • band e (cut i) (cut (i + 1))) * (e r).1 = 0 := by
  rw [sum_mul]
  apply sum_eq_zero
  intro i hi
  rw [smul_mul_assoc, band_mul_eq_zero_of_le e he (habove i hi) (hcut i hi), smul_zero]

section EndpointConvention

/-- The strict lower family of a single atom: the atom at `atom` enters only when `atom < r`. -/
noncomputable def singleAtomLowerFamily (p : StarProjection A) (atom r : ℝ) : StarProjection A :=
  if atom < r then p else ⟨0, IsStarProjection.zero A⟩

/-- The single-atom strict lower family is monotone. -/
theorem monotone_singleAtomLowerFamily (p : StarProjection A) (atom : ℝ) :
    Monotone (singleAtomLowerFamily p atom) := by
  intro r s hrs
  by_cases har : atom < r
  · have has : atom < s := har.trans_le hrs
    simp [singleAtomLowerFamily, har, has]
  · by_cases has : atom < s
    · rw [singleAtomLowerFamily, if_neg har, singleAtomLowerFamily, if_pos has]
      change (0 : A) ≤ p.1
      exact p.2.nonneg
    · simp [singleAtomLowerFamily, har, has]

omit [PartialOrder A] [StarOrderedRing A] in
/-- `E(Iio atom)` excludes an atom at `atom`. -/
@[simp]
theorem singleAtomLowerFamily_at (p : StarProjection A) (atom : ℝ) :
    singleAtomLowerFamily p atom atom = ⟨0, IsStarProjection.zero A⟩ := by
  simp [singleAtomLowerFamily]

omit [PartialOrder A] [StarOrderedRing A] in
/-- The band `[atom,s)` includes the atom at its left endpoint. -/
theorem band_singleAtom_at_of_lt (p : StarProjection A) {atom s : ℝ} (has : atom < s) :
    band (singleAtomLowerFamily p atom) atom s = p.1 := by
  simp [band, singleAtomLowerFamily, has]

omit [PartialOrder A] [StarOrderedRing A] in
/-- A band `[q,atom)` excludes the atom at its right endpoint. -/
theorem band_singleAtom_to_atom_of_le (p : StarProjection A) {q atom : ℝ} (hqa : q ≤ atom) :
    band (singleAtomLowerFamily p atom) q atom = 0 := by
  have hnaq : ¬ atom < q := not_lt.mpr hqa
  simp [band, singleAtomLowerFamily, hnaq]

end EndpointConvention

section TranslatedMoment

/-- The left-endpoint translated moment sum over the first `n` bands. -/
noncomputable def translatedMomentSum (e : ℝ → StarProjection A) (r : ℝ)
    (cut : ℕ → ℝ) (n : ℕ) : A :=
  ∑ i ∈ range n, (r - cut i) • band e (cut i) (cut (i + 1))

/-- The nonnegative part of the translated sum lying below an inserted cutoff `cut k = r`. -/
noncomputable def belowTranslatedSum (e : ℝ → StarProjection A) (r : ℝ)
    (cut : ℕ → ℝ) (k : ℕ) : A :=
  ∑ i ∈ range k, (r - cut i) • band e (cut i) (cut (i + 1))

/-- The magnitude of the negative part above an inserted cutoff, for the following `n` bands. -/
noncomputable def aboveTranslatedMagnitude (e : ℝ → StarProjection A) (r : ℝ)
    (cut : ℕ → ℝ) (k n : ℕ) : A :=
  ∑ i ∈ range n,
    (cut (k + i) - r) • band e (cut (k + i)) (cut (k + i + 1))

omit [PartialOrder A] [StarOrderedRing A] in
/-- Once the cutoff has been inserted at `cut k = r`, the total translated left-endpoint sum is
the below-cut positive sum minus the magnitude of the above-cut negative sum. -/
theorem translatedMomentSum_eq_below_sub_above (e : ℝ → StarProjection A) (r : ℝ)
    (cut : ℕ → ℝ) (k n : ℕ) :
    translatedMomentSum e r cut (k + n) =
      belowTranslatedSum e r cut k - aboveTranslatedMagnitude e r cut k n := by
  rw [translatedMomentSum, belowTranslatedSum, aboveTranslatedMagnitude,
    Finset.sum_range_add]
  rw [sub_eq_add_neg]
  refine congrArg (fun z : A ↦
    (∑ i ∈ range k, (r - cut i) • band e (cut i) (cut (i + 1))) + z) ?_
  rw [← Finset.sum_neg_distrib]
  apply sum_congr rfl
  intro i hi
  rw [← neg_smul]
  congr 1
  ring

/-- The below-cut translated sum is positive. -/
theorem belowTranslatedSum_nonneg (e : ℝ → StarProjection A) (he : Monotone e)
    (r : ℝ) (cut : ℕ → ℝ) (k : ℕ) (hcut : Monotone cut)
    (hkr : cut k = r) : 0 ≤ belowTranslatedSum e r cut k := by
  rw [belowTranslatedSum]
  apply sum_nonneg
  intro i hi
  apply smul_nonneg
  · rw [← hkr]
    exact sub_nonneg.mpr (hcut (Nat.le_of_lt (mem_range.mp hi)))
  · exact (isStarProjection_band e he (hcut (Nat.le_succ i))).nonneg

/-- The magnitude of the above-cut translated sum is positive. -/
theorem aboveTranslatedMagnitude_nonneg (e : ℝ → StarProjection A) (he : Monotone e)
    (r : ℝ) (cut : ℕ → ℝ) (k n : ℕ) (hcut : Monotone cut)
    (hkr : cut k = r) : 0 ≤ aboveTranslatedMagnitude e r cut k n := by
  rw [aboveTranslatedMagnitude]
  apply sum_nonneg
  intro i hi
  apply smul_nonneg
  · rw [← hkr]
    exact sub_nonneg.mpr (hcut (Nat.le_add_right k i))
  · exact (isStarProjection_band e he (hcut (Nat.le_succ (k + i)))).nonneg

/-- The inserted lower projection acts as the identity on the below-cut translated sum. -/
theorem mul_belowTranslatedSum_eq_self (e : ℝ → StarProjection A) (he : Monotone e)
    (r : ℝ) (cut : ℕ → ℝ) (k : ℕ) (hcut : Monotone cut)
    (hkr : cut k = r) :
    (e r).1 * belowTranslatedSum e r cut k = belowTranslatedSum e r cut k := by
  rw [belowTranslatedSum]
  apply mul_weightedBandSum_eq_self_of_below e he r cut (fun i ↦ r - cut i) k
  · exact fun i hi ↦ hcut (Nat.le_succ i)
  · intro i hi
    rw [← hkr]
    exact hcut (Nat.succ_le_iff.mpr (mem_range.mp hi))

/-- The corresponding right identity for the below-cut translated sum. -/
theorem belowTranslatedSum_mul_eq_self (e : ℝ → StarProjection A) (he : Monotone e)
    (r : ℝ) (cut : ℕ → ℝ) (k : ℕ) (hcut : Monotone cut)
    (hkr : cut k = r) :
    belowTranslatedSum e r cut k * (e r).1 = belowTranslatedSum e r cut k := by
  rw [belowTranslatedSum]
  apply weightedBandSum_mul_eq_self_of_below e he r cut (fun i ↦ r - cut i) k
  · exact fun i hi ↦ hcut (Nat.le_succ i)
  · intro i hi
    rw [← hkr]
    exact hcut (Nat.succ_le_iff.mpr (mem_range.mp hi))

/-- The inserted lower projection annihilates the above-cut magnitude from the left. -/
theorem mul_aboveTranslatedMagnitude_eq_zero (e : ℝ → StarProjection A)
    (he : Monotone e) (r : ℝ) (cut : ℕ → ℝ) (k n : ℕ)
    (hcut : Monotone cut) (hkr : cut k = r) :
    (e r).1 * aboveTranslatedMagnitude e r cut k n = 0 := by
  rw [aboveTranslatedMagnitude]
  apply mul_weightedBandSum_eq_zero_of_above e he r (fun i ↦ cut (k + i))
    (fun i ↦ cut (k + i) - r) n
  · exact fun i hi ↦ hcut (Nat.le_succ (k + i))
  · intro i hi
    rw [← hkr]
    exact hcut (Nat.le_add_right k i)

/-- The corresponding right annihilation identity for the above-cut magnitude. -/
theorem aboveTranslatedMagnitude_mul_eq_zero (e : ℝ → StarProjection A)
    (he : Monotone e) (r : ℝ) (cut : ℕ → ℝ) (k n : ℕ)
    (hcut : Monotone cut) (hkr : cut k = r) :
    aboveTranslatedMagnitude e r cut k n * (e r).1 = 0 := by
  rw [aboveTranslatedMagnitude]
  apply weightedBandSum_mul_eq_zero_of_above e he r (fun i ↦ cut (k + i))
    (fun i ↦ cut (k + i) - r) n
  · exact fun i hi ↦ hcut (Nat.le_succ (k + i))
  · intro i hi
    rw [← hkr]
    exact hcut (Nat.le_add_right k i)

/-- The two positive pieces in the translated decomposition are orthogonal. -/
theorem belowTranslatedSum_mul_aboveTranslatedMagnitude_eq_zero
    (e : ℝ → StarProjection A) (he : Monotone e) (r : ℝ)
    (cut : ℕ → ℝ) (k n : ℕ) (hcut : Monotone cut) (hkr : cut k = r) :
    belowTranslatedSum e r cut k * aboveTranslatedMagnitude e r cut k n = 0 := by
  calc
    belowTranslatedSum e r cut k * aboveTranslatedMagnitude e r cut k n =
        (belowTranslatedSum e r cut k * (e r).1) *
          aboveTranslatedMagnitude e r cut k n := by
      rw [belowTranslatedSum_mul_eq_self e he r cut k hcut hkr]
    _ = belowTranslatedSum e r cut k *
        ((e r).1 * aboveTranslatedMagnitude e r cut k n) := by rw [mul_assoc]
    _ = 0 := by rw [mul_aboveTranslatedMagnitude_eq_zero e he r cut k n hcut hkr,
      mul_zero]

/-- Multiplication by the inserted projection extracts the below-cut part of the total translated
sum from the left. -/
theorem mul_translatedMomentSum_eq_below (e : ℝ → StarProjection A) (he : Monotone e)
    (r : ℝ) (cut : ℕ → ℝ) (k n : ℕ) (hcut : Monotone cut) (hkr : cut k = r) :
    (e r).1 * translatedMomentSum e r cut (k + n) = belowTranslatedSum e r cut k := by
  rw [translatedMomentSum_eq_below_sub_above, mul_sub,
    mul_belowTranslatedSum_eq_self e he r cut k hcut hkr,
    mul_aboveTranslatedMagnitude_eq_zero e he r cut k n hcut hkr, sub_zero]

/-- The corresponding right extraction identity. -/
theorem translatedMomentSum_mul_eq_below (e : ℝ → StarProjection A) (he : Monotone e)
    (r : ℝ) (cut : ℕ → ℝ) (k n : ℕ) (hcut : Monotone cut) (hkr : cut k = r) :
    translatedMomentSum e r cut (k + n) * (e r).1 = belowTranslatedSum e r cut k := by
  rw [translatedMomentSum_eq_below_sub_above, sub_mul,
    belowTranslatedSum_mul_eq_self e he r cut k hcut hkr,
    aboveTranslatedMagnitude_mul_eq_zero e he r cut k n hcut hkr, sub_zero]

/-- Finite counterpart of Sakai's positive-part split: after inserting `r`, the positive part of
the translated left-endpoint moment sum is exactly its below-cut piece. -/
theorem posPart_translatedMomentSum_eq_below (e : ℝ → StarProjection A)
    (he : Monotone e) (r : ℝ) (cut : ℕ → ℝ) (k n : ℕ)
    (hcut : Monotone cut) (hkr : cut k = r) :
    (translatedMomentSum e r cut (k + n))⁺ = belowTranslatedSum e r cut k := by
  exact (CFC.posPart_negPart_unique
    (translatedMomentSum_eq_below_sub_above e r cut k n)
    (belowTranslatedSum_mul_aboveTranslatedMagnitude_eq_zero e he r cut k n hcut hkr)
    (belowTranslatedSum_nonneg e he r cut k hcut hkr)
    (aboveTranslatedMagnitude_nonneg e he r cut k n hcut hkr)).1

/-- The finite source-faithful lower bound retains the left-endpoint residual.  If `cut j = s`
and `cut k = r`, then the below-cut translated sum dominates
`(r-s) • (e(s)-e(cut 0))`; passing `cut 0 → -∞` and `e(cut 0) → 0` is a separate
ultraweak/order-limit step. -/
theorem smul_band_le_belowTranslatedSum (e : ℝ → StarProjection A) (he : Monotone e)
    (r s : ℝ) (cut : ℕ → ℝ) {j k : ℕ} (hjk : j ≤ k) (hcut : Monotone cut)
    (hjs : cut j = s) (hkr : cut k = r) :
    (r - s) • band e (cut 0) s ≤ belowTranslatedSum e r cut k := by
  have htel : ∑ i ∈ range j, band e (cut i) (cut (i + 1)) = band e (cut 0) s := by
    calc
      ∑ i ∈ range j, band e (cut i) (cut (i + 1)) =
          (e (cut j)).1 - (e (cut 0)).1 := by
        simpa only [band] using (Finset.sum_range_sub (fun i ↦ (e (cut i)).1) j)
      _ = band e (cut 0) s := by rw [band, hjs]
  calc
    (r - s) • band e (cut 0) s =
        ∑ i ∈ range j, (r - s) • band e (cut i) (cut (i + 1)) := by
      rw [← Finset.smul_sum, htel]
    _ ≤ ∑ i ∈ range j, (r - cut i) • band e (cut i) (cut (i + 1)) := by
      apply sum_le_sum
      intro i hi
      apply smul_le_smul_of_nonneg_right
      · rw [← hjs]
        exact sub_le_sub_left (hcut (Nat.le_of_lt (mem_range.mp hi))) r
      · exact (isStarProjection_band e he (hcut (Nat.le_succ i))).nonneg
    _ ≤ ∑ i ∈ range k, (r - cut i) • band e (cut i) (cut (i + 1)) := by
      apply sum_le_sum_of_subset_of_nonneg (range_mono hjk)
      intro i hi hik
      apply smul_nonneg
      · rw [← hkr]
        exact sub_nonneg.mpr (hcut (Nat.le_of_lt (mem_range.mp hi)))
      · exact (isStarProjection_band e he (hcut (Nat.le_succ i))).nonneg
    _ = belowTranslatedSum e r cut k := by rw [belowTranslatedSum]

/-- Expanded form of the same finite lower bound, displaying the precise residual that must vanish
as the left endpoint tends to `-∞`. -/
theorem smul_projection_sub_residual_le_belowTranslatedSum
    (e : ℝ → StarProjection A) (he : Monotone e) (r s : ℝ)
    (cut : ℕ → ℝ) {j k : ℕ} (hjk : j ≤ k) (hcut : Monotone cut)
    (hjs : cut j = s) (hkr : cut k = r) :
    (r - s) • (e s).1 - (r - s) • (e (cut 0)).1 ≤
      belowTranslatedSum e r cut k := by
  simpa only [band, smul_sub] using
    smul_band_le_belowTranslatedSum e he r s cut hjk hcut hjs hkr

end TranslatedMoment

end Scratch.SakaiUniquenessFinite
