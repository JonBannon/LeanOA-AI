module

public import LeanOA.Ultraweak.NormalCharacterization
public import LeanOA.Ultraweak.WStarAlgebra

@[expose] public section

/-!
# Order characterizations of positive normal functionals

This file relates the established projection-normality predicate to Mathlib's Scott-continuity
predicates. In particular, it supplies the exact bounded directed-positive formulation used in
Sakai's Definition 1.13.1 and connects it to the existing ultraweak-continuity theorem.
-/

open Bornology Set
open scoped ComplexOrder Ultraweak

/-- When a directed family of nonnegative elements has a least upper bound, it is automatically
norm bounded. Consequently the explicit boundedness clause in Sakai's definition of normality is
redundant once preservation is phrased using `ScottContinuousOn`, whose input includes an `IsLUB`
witness. -/
theorem ScottContinuousOn.bounded_nonneg_iff_nonneg
    {A B : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [Preorder B] (f : A → B) :
    ScottContinuousOn {s : Set A | IsBounded s ∧ ∀ x ∈ s, 0 ≤ x} f ↔
      ScottContinuousOn {s : Set A | ∀ x ∈ s, 0 ≤ x} f := by
  constructor
  · intro hf s hs hnon hdir a ha
    apply hf ⟨isBounded_of_bddAbove_of_bddBelow ⟨a, ha.1⟩ ⟨0, hs⟩, hs⟩ hnon hdir ha
  · exact fun hf s hs ↦ hf hs.2

namespace PositiveLinearMap

variable {M P : Type*} [NonUnitalCStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]

private theorem isNormalOnProjections_iff_scottContinuous_of_predual
    (P : Type*) [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]
    (φ : M →ₚ[ℂ] ℂ) :
    φ.IsNormalOnProjections ↔ ScottContinuous φ := by
  letI : IsUnital M := CStarAlgebra.isUnital_of_predual (P := P)
  letI : CStarAlgebra M := IsUnital.toCStarAlgebra
  constructor
  · intro hφ
    have hmem : φ.toContinuousLinearMap ∈ Ultraweak.continuousDual ℂ M P :=
      (φ.isNormalOnProjections_iff_mem_continuousDual (P := P)).1 hφ
    let φu : σ(M, P) →P[ℂ] ℂ := {
      toFun x := φ (ofUltraweak x)
      map_add' x y := by simp
      map_smul' c x := by
        change φ (c • ofUltraweak x) = c * φ (ofUltraweak x)
        rw [map_smul]
        rfl
      monotone' x y hxy := φ.monotone hxy
      cont := (Ultraweak.mem_continuousDual_iff_continuous_ultraweak
        (P := P) φ.toContinuousLinearMap).1 hmem
    }
    intro s hnon hdir a ha
    have haU : IsLUB ((toUltraweak ℂ P) '' s) (toUltraweak ℂ P a) := by
      change IsLUB
        ((Ultraweak.ofUltraweakOrderIso (M := M) (P := P)).symm '' s)
        ((Ultraweak.ofUltraweakOrderIso (M := M) (P := P)).symm a)
      exact (Ultraweak.ofUltraweakOrderIso (M := M) (P := P)).symm.isLUB_image'.2 ha
    have himg := φu.scottContinuous (hnon.image (toUltraweak ℂ P))
      (hdir.mono_comp Ultraweak.monotone_toUltraweak) haU
    have himage : φu '' ((toUltraweak ℂ P) '' s) = φ '' s := by
      ext z
      simp only [Set.mem_image, φu]
      constructor
      · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨x, hx, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨toUltraweak ℂ P x, ⟨x, hx, rfl⟩, rfl⟩
    have hvalue : φu (toUltraweak ℂ P a) = φ a := rfl
    rwa [himage, hvalue] at himg
  · intro hφ s hnon hdir p hp
    have hpM : IsLUB
        ((fun q : {p : M // IsStarProjection p} ↦ q.1) '' s) p.1 :=
      IsStarProjection.isLUB_coe_of_isLUB P s hdir hnon hp
    simpa only [Set.image_image, Function.comp_def] using
      hφ (hnon.image fun q : {p : M // IsStarProjection p} ↦ q.1)
        (hdir.mono_comp fun _ _ h ↦ h) hpM

private theorem isNormalOnProjections_iff_scottContinuousOn_nonneg_of_predual
    (P : Type*) [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]
    (φ : M →ₚ[ℂ] ℂ) :
    φ.IsNormalOnProjections ↔
      ScottContinuousOn {s : Set M | ∀ x ∈ s, 0 ≤ x} φ := by
  letI : IsUnital M := CStarAlgebra.isUnital_of_predual (P := P)
  letI : CStarAlgebra M := IsUnital.toCStarAlgebra
  constructor
  · intro hφ
    exact ((isNormalOnProjections_iff_scottContinuous_of_predual P φ).1 hφ).scottContinuousOn
  · intro hφ s hnon hdir p hp
    let coeProj : {p : M // IsStarProjection p} → M := fun q ↦ q.1
    let t : Set M := coeProj '' s
    have hpM : IsLUB t p.1 :=
      IsStarProjection.isLUB_coe_of_isLUB P s hdir hnon hp
    have himg := hφ (fun x hx ↦ by
      obtain ⟨q, _, rfl⟩ := hx
      exact q.2.nonneg) (hnon.image coeProj)
        (hdir.mono_comp fun _ _ h ↦ h) hpM
    simpa only [t, coeProj, Set.image_image, Function.comp_def] using himg

/-- A positive functional on a W-star algebra is normal on projections exactly when it preserves
all directed suprema which exist. -/
theorem isNormalOnProjections_iff_scottContinuous
    {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] [WStarAlgebra M]
    (φ : M →ₚ[ℂ] ℂ) :
    φ.IsNormalOnProjections ↔ ScottContinuous φ :=
  isNormalOnProjections_iff_scottContinuous_of_predual (WStarAlgebra.predual M) φ

/-- A positive functional on a W-star algebra is normal on projections exactly when it preserves
directed suprema of nonnegative elements. -/
theorem isNormalOnProjections_iff_scottContinuousOn_nonneg
    {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] [WStarAlgebra M]
    (φ : M →ₚ[ℂ] ℂ) :
    φ.IsNormalOnProjections ↔
      ScottContinuousOn {s : Set M | ∀ x ∈ s, 0 ≤ x} φ :=
  isNormalOnProjections_iff_scottContinuousOn_nonneg_of_predual
    (WStarAlgebra.predual M) φ

/-- Sakai's bounded directed-positive definition of normality is equivalent to normality on
projections. Here `Bornology.IsBounded` expresses uniform norm boundedness and
`ScottContinuousOn` expresses preservation of the operator and scalar least upper bounds. -/
theorem isNormalOnProjections_iff_scottContinuousOn_bounded_nonneg
    {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] [WStarAlgebra M]
    (φ : M →ₚ[ℂ] ℂ) :
    φ.IsNormalOnProjections ↔
      ScottContinuousOn {s : Set M | IsBounded s ∧ ∀ x ∈ s, 0 ≤ x} φ :=
  (isNormalOnProjections_iff_scottContinuousOn_nonneg φ).trans
    (ScottContinuousOn.bounded_nonneg_iff_nonneg φ).symm

/-- A positive functional preserves all existing directed suprema exactly when it belongs to the
continuous dual represented by the specified predual. -/
theorem scottContinuous_iff_mem_continuousDual (φ : M →ₚ[ℂ] ℂ) :
    ScottContinuous φ ↔
      φ.toContinuousLinearMap ∈ Ultraweak.continuousDual ℂ M P :=
  (isNormalOnProjections_iff_scottContinuous_of_predual P φ).symm.trans
    (φ.isNormalOnProjections_iff_mem_continuousDual (P := P))

/-- A positive functional preserves the least upper bounds of uniformly bounded directed families
of positive elements exactly when it belongs to the continuous dual represented by the specified
predual. This is the source-facing form of Sakai's Theorem 1.13.2. -/
theorem scottContinuousOn_bounded_nonneg_iff_mem_continuousDual (φ : M →ₚ[ℂ] ℂ) :
    ScottContinuousOn {s : Set M | IsBounded s ∧ ∀ x ∈ s, 0 ≤ x} φ ↔
      φ.toContinuousLinearMap ∈ Ultraweak.continuousDual ℂ M P :=
  (ScottContinuousOn.bounded_nonneg_iff_nonneg φ).trans <|
    (isNormalOnProjections_iff_scottContinuousOn_nonneg_of_predual P φ).symm.trans
      (φ.isNormalOnProjections_iff_mem_continuousDual (P := P))

end PositiveLinearMap
