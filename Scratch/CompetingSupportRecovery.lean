import LeanOA.Ultraweak.SpectralProjection

/-!
# Scratch test: support recovery for a competing lower spectral family

This file isolates the fixed-projection argument implicit in the uniqueness clause of Sakai,
Theorem 1.11.3.  It deliberately introduces no public resolution, integral, or PVM object.

The approximation hypothesis is split into two nets.  The first net represents the part of
`r - a` strictly below `r`; the second represents the negative of the part above `r`.  Both
pieces converge ultraweakly, their difference has the required moment limit, and the finite
pieces are localized by the fixed projection `e r`.  These hypotheses identify the first limit
with the Mathlib-CFC positive part; that identification is proved, not assumed.
-/

open Filter Set
open scoped Topology Ultraweak

namespace Scratch.CompetingSupportRecovery

open WStarAlgebra

variable {M P I : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P]
  [Predual ℂ M P]

/-- Ultraweak limits preserve eventual lower bounds. -/
theorem le_of_tendsto_ultraweak {l : Filter I} [NeBot l] {u : I → M} {x z : M}
    (hu : Tendsto (fun i ↦ toUltraweak ℂ P (u i)) l (nhds (toUltraweak ℂ P x)))
    (hzu : ∀ᶠ i in l, z ≤ u i) :
    z ≤ x := by
  rw [← Ultraweak.toUltraweak_le (P := P)]
  exact ge_of_tendsto hu (hzu.mono fun i hi ↦ by simpa using hi)

/-- Ultraweak limits preserve eventual inequalities when both sides vary. -/
theorem le_of_tendsto_of_tendsto_ultraweak {l : Filter I} [NeBot l]
    {u v : I → M} {x y : M}
    (hu : Tendsto (fun i ↦ toUltraweak ℂ P (u i)) l (nhds (toUltraweak ℂ P x)))
    (hv : Tendsto (fun i ↦ toUltraweak ℂ P (v i)) l (nhds (toUltraweak ℂ P y)))
    (huv : ∀ᶠ i in l, u i ≤ v i) :
    x ≤ y := by
  rw [← Ultraweak.toUltraweak_le (P := P)]
  exact le_of_tendsto_of_tendsto hu hv (huv.mono fun i hi ↦ by simpa using hi)

/-- Fixed left multiplication may be passed through an ultraweak limit.  The formulation with
two approximating nets makes eventual algebraic identities immediately usable. -/
theorem mul_eq_of_tendsto_ultraweak {l : Filter I} [NeBot l] (p : M)
    {u v : I → M} {x y : M}
    (hu : Tendsto (fun i ↦ toUltraweak ℂ P (u i)) l (nhds (toUltraweak ℂ P x)))
    (hv : Tendsto (fun i ↦ toUltraweak ℂ P (v i)) l (nhds (toUltraweak ℂ P y)))
    (huv : ∀ᶠ i in l, p * u i = v i) :
    p * x = y := by
  have hmul :
      Tendsto (fun i ↦ toUltraweak ℂ P (p * u i)) l
        (nhds (toUltraweak ℂ P (p * x))) := by
    simpa only [Function.comp_def, Ultraweak.mulLeftL_apply, ofUltraweak_toUltraweak] using
      (Ultraweak.mulLeftL (P := P) p).continuous.continuousAt.tendsto.comp hu
  have hsame :
      Tendsto (fun i ↦ toUltraweak ℂ P (p * u i)) l
        (nhds (toUltraweak ℂ P y)) :=
    hv.congr' (huv.mono fun i hi ↦ congr_arg (toUltraweak ℂ P) hi.symm)
  exact toUltraweak_inj.mp (tendsto_nhds_unique hmul hsame)

/-- An ultraweakly convergent net of nonnegative elements has nonnegative limit. -/
theorem nonneg_of_tendsto_ultraweak {l : Filter I} [NeBot l] {u : I → M} {x : M}
    (hu : Tendsto (fun i ↦ toUltraweak ℂ P (u i)) l (nhds (toUltraweak ℂ P x)))
    (hux : ∀ᶠ i in l, 0 ≤ u i) :
    0 ≤ x :=
  le_of_tendsto_ultraweak hu hux

/-- The positive and negative limits in a fixed-projection split are the CFC positive and
negative parts of the total moment limit.

This is the approximation-level content of Sakai's assertion that splitting the
Radon--Stieltjes integral at `r` splits `r - a` into its positive and negative parts. -/
theorem posPart_negPart_eq_of_fixedProjection_approximants
    {l : Filter I} [NeBot l] (p : {p : M // IsStarProjection p})
    {u v : I → M} {b c y : M}
    (hu : Tendsto (fun i ↦ toUltraweak ℂ P (u i)) l (nhds (toUltraweak ℂ P b)))
    (hv : Tendsto (fun i ↦ toUltraweak ℂ P (v i)) l (nhds (toUltraweak ℂ P c)))
    (hmoment : Tendsto (fun i ↦ toUltraweak ℂ P (u i - v i)) l
      (nhds (toUltraweak ℂ P y)))
    (hu_nonneg : ∀ᶠ i in l, 0 ≤ u i) (hv_nonneg : ∀ᶠ i in l, 0 ≤ v i)
    (hpu : ∀ᶠ i in l, p.1 * u i = u i) (hpv : ∀ᶠ i in l, p.1 * v i = 0) :
    y⁺ = b ∧ y⁻ = c := by
  have hb : 0 ≤ b := nonneg_of_tendsto_ultraweak hu hu_nonneg
  have hc : 0 ≤ c := nonneg_of_tendsto_ultraweak hv hv_nonneg
  have hpb : p.1 * b = b := mul_eq_of_tendsto_ultraweak p.1 hu hu hpu
  have hpc : p.1 * c = 0 :=
    mul_eq_of_tendsto_ultraweak p.1 hv tendsto_const_nhds hpv
  have hbp : b * p.1 = b := by
    have hstar := congr_arg star hpb
    simpa only [star_mul, p.2.isSelfAdjoint.star_eq, hb.isSelfAdjoint.star_eq] using hstar
  have hbc : b * c = 0 := by
    calc
      b * c = (b * p.1) * c := by rw [hbp]
      _ = b * (p.1 * c) := mul_assoc _ _ _
      _ = 0 := by rw [hpc, mul_zero]
  have hdiff :
      Tendsto (fun i ↦ toUltraweak ℂ P (u i - v i)) l
        (nhds (toUltraweak ℂ P (b - c))) := by
    simpa only [toUltraweak_sub] using hu.sub hv
  have hy : y = b - c :=
    toUltraweak_inj.mp (tendsto_nhds_unique hmoment hdiff)
  exact CFC.posPart_negPart_unique hy hbc hb hc

/-- The separate below-cut and above-cut limits are forced by the total moment limit and the
finite fixed-projection identities.  Thus they need not be assumed as additional integral data. -/
theorem tendsto_split_of_fixedProjection_moment
    {l : Filter I} [NeBot l] (p : {p : M // IsStarProjection p})
    {u v : I → M} {y : M}
    (hmoment : Tendsto (fun i ↦ toUltraweak ℂ P (u i - v i)) l
      (nhds (toUltraweak ℂ P y)))
    (hpu : ∀ᶠ i in l, p.1 * u i = u i) (hpv : ∀ᶠ i in l, p.1 * v i = 0) :
    Tendsto (fun i ↦ toUltraweak ℂ P (u i)) l
        (nhds (toUltraweak ℂ P (p.1 * y))) ∧
      Tendsto (fun i ↦ toUltraweak ℂ P (v i)) l
        (nhds (toUltraweak ℂ P (p.1 * y - y))) := by
  have hmul :
      Tendsto (fun i ↦ toUltraweak ℂ P (p.1 * (u i - v i))) l
        (nhds (toUltraweak ℂ P (p.1 * y))) := by
    simpa only [Function.comp_def, Ultraweak.mulLeftL_apply, ofUltraweak_toUltraweak] using
      (Ultraweak.mulLeftL (P := P) p.1).continuous.continuousAt.tendsto.comp hmoment
  have hpuv : ∀ᶠ i in l, p.1 * (u i - v i) = u i := by
    filter_upwards [hpu, hpv] with i hui hvi
    rw [mul_sub, hui, hvi, sub_zero]
  have hu : Tendsto (fun i ↦ toUltraweak ℂ P (u i)) l
      (nhds (toUltraweak ℂ P (p.1 * y))) :=
    hmul.congr' (hpuv.mono fun i hi ↦ congr_arg (toUltraweak ℂ P) hi)
  have hvRaw :
      Tendsto (fun i ↦ toUltraweak ℂ P (u i - (u i - v i))) l
        (nhds (toUltraweak ℂ P (p.1 * y - y))) := by
    simpa only [toUltraweak_sub] using hu.sub hmoment
  have hv : Tendsto (fun i ↦ toUltraweak ℂ P (v i)) l
      (nhds (toUltraweak ℂ P (p.1 * y - y))) := by
    apply hvRaw.congr'
    exact Eventually.of_forall fun i ↦ by
      abel_nf
  exact ⟨hu, hv⟩

/-- Source-closer positive/negative decomposition: only the total ultraweak moment convergence is
assumed.  Separate convergence of the two pieces follows from fixed multiplication. -/
theorem posPart_negPart_eq_of_fixedProjection_moment
    {l : Filter I} [NeBot l] (p : {p : M // IsStarProjection p})
    {u v : I → M} {y : M}
    (hmoment : Tendsto (fun i ↦ toUltraweak ℂ P (u i - v i)) l
      (nhds (toUltraweak ℂ P y)))
    (hu_nonneg : ∀ᶠ i in l, 0 ≤ u i) (hv_nonneg : ∀ᶠ i in l, 0 ≤ v i)
    (hpu : ∀ᶠ i in l, p.1 * u i = u i) (hpv : ∀ᶠ i in l, p.1 * v i = 0) :
    y⁺ = p.1 * y ∧ y⁻ = p.1 * y - y := by
  obtain ⟨hu, hv⟩ := tendsto_split_of_fixedProjection_moment p hmoment hpu hpv
  exact posPart_negPart_eq_of_fixedProjection_approximants p hu hv hmoment
    hu_nonneg hv_nonneg hpu hpv

/-- A projection whose fixed finite pieces converge to the positive part fixes the positive part
itself. -/
theorem fixedProjection_mul_posPart_of_approximants
    {l : Filter I} [NeBot l] (p : {p : M // IsStarProjection p})
    {u v : I → M} {b c y : M}
    (hu : Tendsto (fun i ↦ toUltraweak ℂ P (u i)) l (nhds (toUltraweak ℂ P b)))
    (hv : Tendsto (fun i ↦ toUltraweak ℂ P (v i)) l (nhds (toUltraweak ℂ P c)))
    (hmoment : Tendsto (fun i ↦ toUltraweak ℂ P (u i - v i)) l
      (nhds (toUltraweak ℂ P y)))
    (hu_nonneg : ∀ᶠ i in l, 0 ≤ u i) (hv_nonneg : ∀ᶠ i in l, 0 ≤ v i)
    (hpu : ∀ᶠ i in l, p.1 * u i = u i) (hpv : ∀ᶠ i in l, p.1 * v i = 0) :
    p.1 * y⁺ = y⁺ := by
  have hpos :=
    (posPart_negPart_eq_of_fixedProjection_approximants p hu hv hmoment
      hu_nonneg hv_nonneg hpu hpv).1
  rw [hpos]
  exact mul_eq_of_tendsto_ultraweak p.1 hu hu hpu

/-- The fixed projection from a source-level moment split fixes the CFC positive part. -/
theorem fixedProjection_mul_posPart_of_moment
    {l : Filter I} [NeBot l] (p : {p : M // IsStarProjection p})
    {u v : I → M} {y : M}
    (hmoment : Tendsto (fun i ↦ toUltraweak ℂ P (u i - v i)) l
      (nhds (toUltraweak ℂ P y)))
    (hu_nonneg : ∀ᶠ i in l, 0 ≤ u i) (hv_nonneg : ∀ᶠ i in l, 0 ≤ v i)
    (hpu : ∀ᶠ i in l, p.1 * u i = u i) (hpv : ∀ᶠ i in l, p.1 * v i = 0) :
    p.1 * y⁺ = y⁺ := by
  rw [(posPart_negPart_eq_of_fixedProjection_moment p hmoment hu_nonneg
    hv_nonneg hpu hpv).1, ← mul_assoc, p.2.isIdempotentElem.eq]

/-- Monotonicity plus one ultraweak approach from strictly below identifies the value at the cut
as the least upper bound of all earlier projections. -/
theorem isLUB_image_Iio_of_tendsto_below
    (e : ℝ → {p : M // IsStarProjection p}) (he : Monotone e) (r : ℝ)
    {J : Type*} {l : Filter J} [NeBot l] (f : J → ℝ)
    (hf : ∀ᶠ j in l, f j < r)
    (hlim : Tendsto (fun j ↦ toUltraweak ℂ P (e (f j)).1) l
      (nhds (toUltraweak ℂ P (e r).1))) :
    IsLUB (e '' Iio r) (e r) := by
  constructor
  · rintro q ⟨s, hsr, rfl⟩
    exact he hsr.le
  · intro q hq
    change (e r).1 ≤ q.1
    exact Ultraweak.monotone_ofUltraweak (P := P) <|
      le_of_tendsto_of_tendsto hlim tendsto_const_nhds <|
        hf.mono fun j hj ↦ Ultraweak.monotone_toUltraweak (P := P) (hq ⟨f j, hj, rfl⟩)

/-- Sakai's sequential continuity-from-below clause implies the exact `Iio` least-upper-bound
law at every cut. -/
theorem isLUB_image_Iio_of_monotone_of_continuousBelow
    (e : ℝ → {p : M // IsStarProjection p}) (he : Monotone e)
    (hcont : ∀ (f : ℕ → ℝ) (r : ℝ), Monotone f → Tendsto f atTop (nhds r) →
      Tendsto (fun n ↦ toUltraweak ℂ P (e (f n)).1) atTop
        (nhds (toUltraweak ℂ P (e r).1)))
    (r : ℝ) : IsLUB (e '' Iio r) (e r) := by
  let f : ℕ → ℝ := fun n ↦ r - 1 / ((n : ℝ) + 1)
  have hf_mono : Monotone f := by
    intro m n hmn
    dsimp [f]
    gcongr
  have hf_tendsto : Tendsto f atTop (nhds r) := by
    simpa [f] using tendsto_const_nhds.sub
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  apply isLUB_image_Iio_of_tendsto_below (P := P) (l := atTop) e he r f
  · exact Eventually.of_forall fun n ↦ by
      dsimp [f]
      exact sub_lt_self r (one_div_pos.mpr (by positivity))
  · exact hcont f r hf_mono hf_tendsto

/-- A vanishing left-endpoint projection gives the varying lower-bound limit used in the
source-faithful support argument. -/
theorem tendsto_real_smul_sub_of_tendsto_zero
    {l : Filter I} (c : ℝ) (x : M) {z : I → M}
    (hz : Tendsto (fun i ↦ toUltraweak ℂ P (z i)) l
      (nhds (toUltraweak ℂ P 0))) :
    Tendsto (fun i ↦ toUltraweak ℂ P (c • (x - z i))) l
      (nhds (toUltraweak ℂ P (c • x))) := by
  have hsub : Tendsto (fun i ↦ toUltraweak ℂ P (x - z i)) l
      (nhds (toUltraweak ℂ P x)) := by
    simpa only [toUltraweak_sub, toUltraweak_zero, sub_zero] using
      (tendsto_const_nhds.sub hz : Tendsto
        (fun i ↦ toUltraweak ℂ P x - toUltraweak ℂ P (z i)) l
        (nhds (toUltraweak ℂ P x - toUltraweak ℂ P 0)))
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  simp only [toUltraweak_smul]
  convert hsub.const_smul (c : ℂ) using 1 <;> rfl

variable [WStarAlgebra M]

/-- A positive element dominating a positive scalar multiple of a projection has support above
that projection. -/
theorem isStarProjection_le_support_of_smul_le
    {x : M} (hx : 0 ≤ x) (p : {p : M // IsStarProjection p}) {c : ℝ}
    (hc : 0 < c) (hcx : c • p.1 ≤ x) :
    p ≤ support ⟨x, hx.isSelfAdjoint⟩ := by
  have hpSupport : leftSupport p.1 = p := by
    apply le_antisymm
    · exact (leftSupport_le_iff p.1 p).2 p.2.isIdempotentElem.eq
    · exact (p.2.le_iff_mul_eq_right (leftSupport p.1).2).2 (leftSupport_mul p.1)
  have hcp : leftSupport (c • p.1) = p := by
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), leftSupport_smul]
    · exact hpSupport
    · exact Complex.ofReal_ne_zero.mpr hc.ne'
  have hmono : leftSupport (c • p.1) ≤ leftSupport x :=
    leftSupport_mono_of_nonneg (smul_nonneg hc.le p.2.nonneg) hcx
  simpa only [support, hcp] using hmono

/-- The topology-free final support step: upper localization, strict lower bounds, and continuity
from below recover the projection at the cut. -/
theorem support_eq_family_at_of_below
    (e : ℝ → {p : M // IsStarProjection p}) (r : ℝ) {x : M} (hx : 0 ≤ x)
    (herx : (e r).1 * x = x)
    (hlower : ∀ s < r, ∃ c : ℝ, 0 < c ∧ c • (e s).1 ≤ x)
    (hbelow : IsLUB (e '' Iio r) (e r)) :
    support ⟨x, hx.isSelfAdjoint⟩ = e r := by
  apply le_antisymm
  · exact (leftSupport_le_iff x (e r)).2 herx
  · apply hbelow.2
    rintro q ⟨s, hsr, rfl⟩
    obtain ⟨c, hc, hcq⟩ := hlower s hsr
    exact isStarProjection_le_support_of_smul_le hx (e s) hc hcq

/-- First support inequality.  The CFC positive part is carried by the projection used in the
finite below/above split. -/
theorem support_spectralPositivePart_le_of_fixedProjection_moment
    {l : Filter I} [NeBot l] (p : {p : M // IsStarProjection p})
    (a : selfAdjoint M) (r : ℝ) {u v : I → M}
    (hmoment : Tendsto (fun i ↦ toUltraweak ℂ P (u i - v i)) l
      (nhds (toUltraweak ℂ P (algebraMap ℝ M r - a.1))))
    (hu_nonneg : ∀ᶠ i in l, 0 ≤ u i) (hv_nonneg : ∀ᶠ i in l, 0 ≤ v i)
    (hpu : ∀ᶠ i in l, p.1 * u i = u i) (hpv : ∀ᶠ i in l, p.1 * v i = 0) :
    support
        ⟨CStarAlgebra.spectralPositivePart a r,
          (CStarAlgebra.spectralPositivePart_nonneg a r).isSelfAdjoint⟩ ≤ p := by
  change leftSupport (CStarAlgebra.spectralPositivePart a r) ≤ p
  rw [leftSupport_le_iff]
  rw [CStarAlgebra.spectralPositivePart_eq_posPart]
  exact fixedProjection_mul_posPart_of_moment p hmoment hu_nonneg hv_nonneg hpu hpv

/-- Second support inequality at a strictly earlier cut.  The lower comparison may itself vary
with the approximating division; order closedness passes both sides to their ultraweak limits. -/
theorem competing_le_support_spectralPositivePart_of_fixedProjection_moment
    {l : Filter I} [NeBot l] (e : ℝ → {p : M // IsStarProjection p})
    (a : selfAdjoint M) {s r : ℝ} (hsr : s < r) {u v lower : I → M}
    (hmoment : Tendsto (fun i ↦ toUltraweak ℂ P (u i - v i)) l
      (nhds (toUltraweak ℂ P (algebraMap ℝ M r - a.1))))
    (hu_nonneg : ∀ᶠ i in l, 0 ≤ u i) (hv_nonneg : ∀ᶠ i in l, 0 ≤ v i)
    (hpu : ∀ᶠ i in l, (e r).1 * u i = u i)
    (hpv : ∀ᶠ i in l, (e r).1 * v i = 0)
    (hlower_tendsto : Tendsto (fun i ↦ toUltraweak ℂ P (lower i)) l
      (nhds (toUltraweak ℂ P ((r - s) • (e s).1))))
    (hlower_le : ∀ᶠ i in l, lower i ≤ u i) :
    e s ≤ support
      ⟨CStarAlgebra.spectralPositivePart a r,
        (CStarAlgebra.spectralPositivePart_nonneg a r).isSelfAdjoint⟩ := by
  let y : M := algebraMap ℝ M r - a.1
  obtain ⟨hu, _hv⟩ := tendsto_split_of_fixedProjection_moment (e r) hmoment hpu hpv
  have hparts := posPart_negPart_eq_of_fixedProjection_moment (e r) hmoment
    hu_nonneg hv_nonneg hpu hpv
  have htarget : CStarAlgebra.spectralPositivePart a r = (e r).1 * y := by
    rw [CStarAlgebra.spectralPositivePart_eq_posPart]
    exact hparts.1
  apply isStarProjection_le_support_of_smul_le
    (CStarAlgebra.spectralPositivePart_nonneg a r) (e s) (sub_pos.mpr hsr)
  rw [htarget]
  exact le_of_tendsto_of_tendsto_ultraweak hlower_tendsto hu hlower_le

/-- Pointwise support recovery for a competing lower family from explicit, noncircular
ultraweak moment data.

The conclusion identifies the support of the existing Mathlib-CFC truncated-affine value.  No
separate convergence to that value is assumed: the two split limits are forced by the total
moment convergence and fixed-projection identities.  The lower comparison is allowed to vary
with the approximation, as it must when the left endpoint tends to `-∞` but is never exactly
normalized to zero. -/
theorem support_spectralPositivePart_eq_of_fixedProjection_moment
    {l : Filter I} [NeBot l] (e : ℝ → {p : M // IsStarProjection p})
    (a : selfAdjoint M) (r : ℝ) {u v : I → M} {lower : ℝ → I → M}
    (hmoment : Tendsto (fun i ↦ toUltraweak ℂ P (u i - v i)) l
      (nhds (toUltraweak ℂ P (algebraMap ℝ M r - a.1))))
    (hu_nonneg : ∀ᶠ i in l, 0 ≤ u i) (hv_nonneg : ∀ᶠ i in l, 0 ≤ v i)
    (hpu : ∀ᶠ i in l, (e r).1 * u i = u i)
    (hpv : ∀ᶠ i in l, (e r).1 * v i = 0)
    (hlower_tendsto : ∀ s < r,
      Tendsto (fun i ↦ toUltraweak ℂ P (lower s i)) l
        (nhds (toUltraweak ℂ P ((r - s) • (e s).1))))
    (hlower_le : ∀ s < r, ∀ᶠ i in l, lower s i ≤ u i)
    (hbelow : IsLUB (e '' Iio r) (e r)) :
    support
        ⟨CStarAlgebra.spectralPositivePart a r,
          (CStarAlgebra.spectralPositivePart_nonneg a r).isSelfAdjoint⟩ = e r := by
  apply le_antisymm
  · exact support_spectralPositivePart_le_of_fixedProjection_moment
      (e r) a r hmoment hu_nonneg hv_nonneg hpu hpv
  · apply hbelow.2
    rintro q ⟨s, hsr, rfl⟩
    exact competing_le_support_spectralPositivePart_of_fixedProjection_moment
      e a hsr hmoment hu_nonneg hv_nonneg hpu hpv
        (hlower_tendsto s hsr) (hlower_le s hsr)

/-- The competing projection at one cut equals the canonical strict-lower-half-line spectral
projection. -/
theorem competing_eq_spectralProjectionIio_of_fixedProjection_moment
    {l : Filter I} [NeBot l] (e : ℝ → {p : M // IsStarProjection p})
    (a : selfAdjoint M) (r : ℝ) {u v : I → M} {lower : ℝ → I → M}
    (hmoment : Tendsto (fun i ↦ toUltraweak ℂ P (u i - v i)) l
      (nhds (toUltraweak ℂ P (algebraMap ℝ M r - a.1))))
    (hu_nonneg : ∀ᶠ i in l, 0 ≤ u i) (hv_nonneg : ∀ᶠ i in l, 0 ≤ v i)
    (hpu : ∀ᶠ i in l, (e r).1 * u i = u i)
    (hpv : ∀ᶠ i in l, (e r).1 * v i = 0)
    (hlower_tendsto : ∀ s < r,
      Tendsto (fun i ↦ toUltraweak ℂ P (lower s i)) l
        (nhds (toUltraweak ℂ P ((r - s) • (e s).1))))
    (hlower_le : ∀ s < r, ∀ᶠ i in l, lower s i ≤ u i)
    (hbelow : IsLUB (e '' Iio r) (e r)) :
    e r = spectralProjectionIio a r := by
  exact (support_spectralPositivePart_eq_of_fixedProjection_moment
    e a r hmoment hu_nonneg hv_nonneg hpu hpv hlower_tendsto hlower_le hbelow).symm

/-- Source-shaped pointwise uniqueness: monotonicity and Sakai's sequential continuity clause
supply the `Iio` LUB used by support recovery. -/
theorem competing_eq_spectralProjectionIio_of_continuousBelow
    {l : Filter I} [NeBot l] (e : ℝ → {p : M // IsStarProjection p})
    (he : Monotone e)
    (hcont : ∀ (f : ℕ → ℝ) (t : ℝ), Monotone f → Tendsto f atTop (nhds t) →
      Tendsto (fun n ↦ toUltraweak ℂ P (e (f n)).1) atTop
        (nhds (toUltraweak ℂ P (e t).1)))
    (a : selfAdjoint M) (r : ℝ) {u v : I → M} {lower : ℝ → I → M}
    (hmoment : Tendsto (fun i ↦ toUltraweak ℂ P (u i - v i)) l
      (nhds (toUltraweak ℂ P (algebraMap ℝ M r - a.1))))
    (hu_nonneg : ∀ᶠ i in l, 0 ≤ u i) (hv_nonneg : ∀ᶠ i in l, 0 ≤ v i)
    (hpu : ∀ᶠ i in l, (e r).1 * u i = u i)
    (hpv : ∀ᶠ i in l, (e r).1 * v i = 0)
    (hlower_tendsto : ∀ s < r,
      Tendsto (fun i ↦ toUltraweak ℂ P (lower s i)) l
        (nhds (toUltraweak ℂ P ((r - s) • (e s).1))))
    (hlower_le : ∀ s < r, ∀ᶠ i in l, lower s i ≤ u i) :
    e r = spectralProjectionIio a r := by
  apply competing_eq_spectralProjectionIio_of_fixedProjection_moment
    e a r hmoment hu_nonneg hv_nonneg hpu hpv hlower_tendsto hlower_le
  exact isLUB_image_Iio_of_monotone_of_continuousBelow e he hcont r

/-- Pointwise recovery at every cut gives uniqueness of the whole competing family. -/
theorem competing_family_unique_of_pointwise_recovery
    {e e' : ℝ → {p : M // IsStarProjection p}} (a : selfAdjoint M)
    (he : ∀ r, e r = spectralProjectionIio a r)
    (he' : ∀ r, e' r = spectralProjectionIio a r) :
    e = e' := by
  funext r
  exact (he r).trans (he' r).symm

end Scratch.CompetingSupportRecovery
