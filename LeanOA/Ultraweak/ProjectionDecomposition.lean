module

public import LeanOA.Ultraweak.Multiplication
public import LeanOA.Ultraweak.OrderClosed

@[expose] public section

/-!
# Ultraweak decompositions localized by a fixed projection

This file isolates a general limit argument for a difference of two positive nets when one fixed
projection extracts the first part from each difference. Separate ultraweak continuity forces the
two pieces to converge individually; closedness of the positive cone and orthogonality then
identify their limits with the positive and negative parts of the total limit.
-/

open Filter
open scoped Topology Ultraweak

namespace Ultraweak

variable {M P I : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]

/-- If a fixed element extracts `uᵢ` from `uᵢ - vᵢ`, convergence of the difference forces
convergence of the two pieces separately. -/
theorem tendsto_parts_of_tendsto_sub
    {l : Filter I} {p : M} {u v : I → M} {y : M}
    (hmoment : Tendsto (fun i ↦ toUltraweak ℂ P (u i - v i)) l
      (𝓝 (toUltraweak ℂ P y)))
    (hextract : ∀ᶠ i in l, p * (u i - v i) = u i) :
    Tendsto (fun i ↦ toUltraweak ℂ P (u i)) l
        (𝓝 (toUltraweak ℂ P (p * y))) ∧
      Tendsto (fun i ↦ toUltraweak ℂ P (v i)) l
        (𝓝 (toUltraweak ℂ P (p * y - y))) := by
  have hmul : Tendsto (fun i ↦ toUltraweak ℂ P (p * (u i - v i))) l
      (𝓝 (toUltraweak ℂ P (p * y))) := by
    simpa only [toUltraweak_mul] using hmoment.const_mul (toUltraweak ℂ P p)
  have hu : Tendsto (fun i ↦ toUltraweak ℂ P (u i)) l
      (𝓝 (toUltraweak ℂ P (p * y))) := by
    apply hmul.congr'
    exact hextract.mono fun i hi ↦ congr_arg (toUltraweak ℂ P) hi
  refine ⟨hu, ?_⟩
  have hv := hu.sub hmoment
  apply hv.congr'
  filter_upwards with i
  simp only [toUltraweak_sub, sub_sub_cancel]

/-- If the two parts of an ultraweakly convergent difference are eventually nonnegative and a
fixed star projection extracts the first part, their limits are the positive and negative parts
of the total limit. -/
theorem posPart_negPart_eq_of_tendsto_sub_of_isStarProjection
    {l : Filter I} [NeBot l] {p : M} (hp : IsStarProjection p) {u v : I → M} {y : M}
    (hmoment : Tendsto (fun i ↦ toUltraweak ℂ P (u i - v i)) l
      (𝓝 (toUltraweak ℂ P y)))
    (hu_nonneg : ∀ᶠ i in l, 0 ≤ u i) (hv_nonneg : ∀ᶠ i in l, 0 ≤ v i)
    (hextract : ∀ᶠ i in l, p * (u i - v i) = u i) :
    y⁺ = p * y ∧ y⁻ = p * y - y := by
  obtain ⟨hu, hv⟩ := tendsto_parts_of_tendsto_sub hmoment hextract
  have hb : 0 ≤ p * y := by
    apply monotone_ofUltraweak (P := P)
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hu <|
      hu_nonneg.mono fun _ hi ↦ monotone_toUltraweak (P := P) hi
  have hc : 0 ≤ p * y - y := by
    apply monotone_ofUltraweak (P := P)
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hv <|
      hv_nonneg.mono fun _ hi ↦ monotone_toUltraweak (P := P) hi
  have hpb : p * (p * y) = p * y := by rw [← mul_assoc, hp.isIdempotentElem.eq]
  have hpc : p * (p * y - y) = 0 := by rw [mul_sub, hpb, sub_self]
  have hbp : (p * y) * p = p * y := by
    have hstar := congr_arg star hpb
    simpa only [star_mul, hp.isSelfAdjoint.star_eq, hb.isSelfAdjoint.star_eq] using hstar
  have horth : (p * y) * (p * y - y) = 0 := by
    calc
      (p * y) * (p * y - y) = ((p * y) * p) * (p * y - y) := by rw [hbp]
      _ = (p * y) * (p * (p * y - y)) := by rw [mul_assoc]
      _ = 0 := by rw [hpc, mul_zero]
  exact CFC.posPart_negPart_unique (by abel) horth hb hc

end Ultraweak
