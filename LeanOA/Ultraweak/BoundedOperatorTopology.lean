module

public import LeanOA.Ultraweak.BoundedOperatorClosedness

/-!
# Bounded operator topologies on norm-bounded sets

This file formalizes the weak-family half of Sakai, Proposition 1.15.2. For a WOT-closed,
possibly nonunital self-adjoint operator algebra `N`, the weak operator topology, Sakai's
coefficient-series sigma-weak operator topology, and the intrinsic weak-star topology
`sigma(N, N_*)` agree on every zero-centered norm-closed ball.

Sakai calls these sets "bounded spheres". In the source proof this means closed balls, not norm
spheres: compactness of the unit ball is the key input. The primary API consists of
homeomorphisms between the three closed-ball carriers, so it is filter-general and not restricted
to sequences. The strong-family half of Proposition 1.15.2 is not claimed here.
-/

@[expose] public section

open Metric Set Filter
open scoped InnerProductSpace Ultraweak

noncomputable section

namespace ContinuousLinearMapWOT

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "BH" => H →L[ℂ] H
local notation "SeriesCore" => ContinuousLinearMap.vectorFunctionalSeriesSpan (H := H)
local notation "SigmaWOT" =>
  WeakBilin (Ultraweak.testPairing (M := BH) SeriesCore)

/-- The canonical identity from Sakai's coefficient-series sigma-WOT carrier to Mathlib's WOT
carrier is injective. -/
theorem vectorFunctionalSeriesWeakToWOTL_injective :
    Function.Injective (vectorFunctionalSeriesWeakToWOTL (H := H)) := by
  intro x y hxy
  apply (WeakBilin.linearEquiv ℂ
    (Ultraweak.testPairing (M := BH) SeriesCore)).injective
  exact congrArg ContinuousLinearMapWOT.toCLM hxy

/-- Sakai's coefficient-series sigma-weak operator topology is Hausdorff. -/
instance : T2Space SigmaWOT :=
  T2Space.of_injective_continuous
    (vectorFunctionalSeriesWeakToWOTL_injective (H := H))
    (vectorFunctionalSeriesWeakToWOTL (H := H)).continuous

end ContinuousLinearMapWOT

namespace BoundedOperatorTopology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "BH" => H →L[ℂ] H
local notation "BHPredual" => ContinuousLinearMap.VectorFunctionalPredual ℂ H H
local notation "SeriesCore" => ContinuousLinearMap.vectorFunctionalSeriesSpan (H := H)
local notation "SigmaWOT" =>
  WeakBilin (Ultraweak.testPairing (M := BH) SeriesCore)

/-- The part of a closed norm ball lying in a specified set, carried by the ambient
concrete-predual ultraweak topology. -/
abbrev AmbientUltraweakClosedBall (s : Set BH) (r : ℝ) :=
  {T : σ(BH, BHPredual) // ofUltraweak T ∈ s ∧ ‖ofUltraweak T‖ ≤ r}

/-- The part of a closed norm ball lying in a specified set, carried by Sakai's
coefficient-series sigma-WOT. -/
abbrev SigmaWOTClosedBall (s : Set BH) (r : ℝ) :=
  {T : SigmaWOT //
    WeakBilin.linearEquiv ℂ (Ultraweak.testPairing (M := BH) SeriesCore) T ∈ s ∧
      ‖WeakBilin.linearEquiv ℂ (Ultraweak.testPairing (M := BH) SeriesCore) T‖ ≤ r}

/-- The part of a closed norm ball lying in a specified set, carried by Mathlib's weak operator
topology. -/
abbrev WOTClosedBall (s : Set BH) (r : ℝ) :=
  {T : H →WOT[ℂ] H // T.toCLM ∈ s ∧ ‖T.toCLM‖ ≤ r}

/-- The carrier equivalence underlying the bounded ambient-ultraweak/sigma-WOT comparison. -/
def ambientUltraweakSigmaWOTClosedBallEquiv
    (s : Set BH) (r : ℝ) :
    AmbientUltraweakClosedBall s r ≃ SigmaWOTClosedBall s r where
  toFun T := ⟨ContinuousLinearMap.vectorFunctionalSeriesWeakOfUltraweakL T.1,
    T.2.1, T.2.2⟩
  invFun T := ⟨toUltraweak ℂ BHPredual
      (WeakBilin.linearEquiv ℂ (Ultraweak.testPairing (M := BH) SeriesCore) T.1),
    T.2.1, T.2.2⟩
  left_inv T := by apply Subtype.ext; rfl
  right_inv T := by apply Subtype.ext; rfl

/-- The canonical bounded identity from ambient ultraweak topology to coefficient-series
sigma-WOT is continuous. -/
lemma continuous_ambientUltraweakSigmaWOTClosedBallEquiv
    (s : Set BH) (r : ℝ) :
    Continuous (ambientUltraweakSigmaWOTClosedBallEquiv s r) := by
  apply Continuous.subtype_mk
  exact (ContinuousLinearMap.vectorFunctionalSeriesWeakOfUltraweakL
    (H := H)).continuous.comp continuous_subtype_val

/-- An ultraweakly closed part of a norm-closed ball is compact in the ambient ultraweak
topology. -/
lemma compactSpace_ambientUltraweakClosedBall
    (s : Set BH)
    (hs : IsClosed (ofUltraweak ⁻¹' s : Set σ(BH, BHPredual))) (r : ℝ) :
    CompactSpace (AmbientUltraweakClosedBall s r) :=
  isCompact_iff_compactSpace.mp <| by
    convert (Ultraweak.isCompact_closedBall ℂ BHPredual (0 : BH) r).inter_left hs
      using 1
    ext T
    change (ofUltraweak T ∈ s ∧ ‖ofUltraweak T‖ ≤ r) ↔
      (ofUltraweak T ∈ s ∧ dist (ofUltraweak T) 0 ≤ r)
    rw [dist_zero_right]

/-- On a closed part of a norm ball, the ambient concrete-predual ultraweak topology and Sakai's
coefficient-series sigma-WOT agree. -/
def ambientUltraweakSigmaWOTClosedBallHomeomorph
    (s : Set BH)
    (hs : IsClosed (ofUltraweak ⁻¹' s : Set σ(BH, BHPredual))) (r : ℝ) :
    AmbientUltraweakClosedBall s r ≃ₜ SigmaWOTClosedBall s r := by
  letI : CompactSpace (AmbientUltraweakClosedBall s r) :=
    compactSpace_ambientUltraweakClosedBall s hs r
  exact (continuous_ambientUltraweakSigmaWOTClosedBallEquiv s r).homeoOfEquivCompactToT2

/-- The carrier equivalence underlying the bounded sigma-WOT/WOT comparison. -/
def sigmaWOTWOTClosedBallEquiv
    (s : Set BH) (r : ℝ) :
    SigmaWOTClosedBall s r ≃ WOTClosedBall s r where
  toFun T := ⟨ContinuousLinearMapWOT.vectorFunctionalSeriesWeakToWOTL T.1,
    T.2.1, T.2.2⟩
  invFun T := ⟨(WeakBilin.linearEquiv ℂ
      (Ultraweak.testPairing (M := BH) SeriesCore)).symm T.1.toCLM,
    T.2.1, T.2.2⟩
  left_inv T := by apply Subtype.ext; rfl
  right_inv T := by apply Subtype.ext; rfl

/-- The canonical bounded identity from coefficient-series sigma-WOT to WOT is continuous. -/
lemma continuous_sigmaWOTWOTClosedBallEquiv
    (s : Set BH) (r : ℝ) :
    Continuous (sigmaWOTWOTClosedBallEquiv s r) := by
  apply Continuous.subtype_mk
  exact (ContinuousLinearMapWOT.vectorFunctionalSeriesWeakToWOTL
    (H := H)).continuous.comp continuous_subtype_val

/-- On a closed part of a norm ball, Sakai's coefficient-series sigma-WOT and Mathlib's WOT
agree. -/
def sigmaWOTWOTClosedBallHomeomorph
    (s : Set BH)
    (hs : IsClosed (ofUltraweak ⁻¹' s : Set σ(BH, BHPredual))) (r : ℝ) :
    SigmaWOTClosedBall s r ≃ₜ WOTClosedBall s r := by
  letI : CompactSpace (AmbientUltraweakClosedBall s r) :=
    compactSpace_ambientUltraweakClosedBall s hs r
  letI : CompactSpace (SigmaWOTClosedBall s r) :=
    (ambientUltraweakSigmaWOTClosedBallHomeomorph s hs r).compactSpace
  exact (continuous_sigmaWOTWOTClosedBallEquiv s r).homeoOfEquivCompactToT2

/-- On a closed part of a norm ball, the ambient concrete-predual ultraweak topology and
Mathlib's WOT agree. -/
def ambientUltraweakWOTClosedBallHomeomorph
    (s : Set BH)
    (hs : IsClosed (ofUltraweak ⁻¹' s : Set σ(BH, BHPredual))) (r : ℝ) :
    AmbientUltraweakClosedBall s r ≃ₜ WOTClosedBall s r :=
  (ambientUltraweakSigmaWOTClosedBallHomeomorph s hs r).trans
    (sigmaWOTWOTClosedBallHomeomorph s hs r)

end BoundedOperatorTopology

namespace NonUnitalStarSubalgebra

open BoundedOperatorTopology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "BH" => H →L[ℂ] H
local notation "BHPredual" => ContinuousLinearMap.VectorFunctionalPredual ℂ H H
local notation "SeriesCore" => ContinuousLinearMap.vectorFunctionalSeriesSpan (H := H)

/-- The intrinsic weak-star topology `sigma(N, N_*)`, where `N_*` is the quotient of the
concrete predual of `B(H)` by the preannihilator of `N`. -/
abbrev InducedUltraweak (N : NonUnitalStarSubalgebra ℂ BH)
    (hN : N.IsUltraweakClosed (P := BHPredual)) :=
  @Ultraweak ℂ N
    (BHPredual ⧸ Ultraweak.preannihilator (P := BHPredual) N.toSubmodule)
    _ _ _ _ _ (IsUltraweakClosed.inducedPredual N hN)

/-- A closed norm ball in the intrinsic weak-star topology `sigma(N, N_*)`. -/
abbrev InducedUltraweakClosedBall (N : NonUnitalStarSubalgebra ℂ BH)
    (hN : N.IsUltraweakClosed (P := BHPredual)) (r : ℝ) :=
  {T : InducedUltraweak N hN // ‖(show N from T)‖ ≤ r}

/-- On a closed norm ball in an ultraweakly closed operator algebra, the ambient concrete-predual
ultraweak topology and Sakai's coefficient-series sigma-WOT agree. -/
def IsUltraweakClosed.ambientUltraweakSigmaWOTClosedBallHomeomorph
    (N : NonUnitalStarSubalgebra ℂ BH)
    (hN : N.IsUltraweakClosed (P := BHPredual)) (r : ℝ) :
    AmbientUltraweakClosedBall (N : Set BH) r ≃ₜ
      SigmaWOTClosedBall (N : Set BH) r :=
  BoundedOperatorTopology.ambientUltraweakSigmaWOTClosedBallHomeomorph (N : Set BH)
    hN.isClosed_ambientPreimage r

/-- On a closed norm ball in an ultraweakly closed operator algebra, Sakai's coefficient-series
sigma-WOT and Mathlib's WOT agree. -/
def IsUltraweakClosed.sigmaWOTWOTClosedBallHomeomorph
    (N : NonUnitalStarSubalgebra ℂ BH)
    (hN : N.IsUltraweakClosed (P := BHPredual)) (r : ℝ) :
    SigmaWOTClosedBall (N : Set BH) r ≃ₜ WOTClosedBall (N : Set BH) r :=
  BoundedOperatorTopology.sigmaWOTWOTClosedBallHomeomorph (N : Set BH)
    hN.isClosed_ambientPreimage r

/-- On a closed norm ball in an ultraweakly closed operator algebra, the ambient concrete-predual
ultraweak topology and Mathlib's WOT agree. -/
def IsUltraweakClosed.ambientUltraweakWOTClosedBallHomeomorph
    (N : NonUnitalStarSubalgebra ℂ BH)
    (hN : N.IsUltraweakClosed (P := BHPredual)) (r : ℝ) :
    AmbientUltraweakClosedBall (N : Set BH) r ≃ₜ WOTClosedBall (N : Set BH) r :=
  BoundedOperatorTopology.ambientUltraweakWOTClosedBallHomeomorph (N : Set BH)
    hN.isClosed_ambientPreimage r

/-- The intrinsic quotient-predual topology on `N` agrees on closed norm balls with the ambient
concrete-predual ultraweak topology. -/
def IsUltraweakClosed.inducedAmbientUltraweakClosedBallHomeomorph
    (N : NonUnitalStarSubalgebra ℂ BH)
    (hN : N.IsUltraweakClosed (P := BHPredual)) (r : ℝ) :
    InducedUltraweakClosedBall N hN r ≃ₜ AmbientUltraweakClosedBall (N : Set BH) r := by
  letI : Predual ℂ N
      (BHPredual ⧸ Ultraweak.preannihilator (P := BHPredual) N.toSubmodule) :=
    hN.inducedPredual N
  let e := hN.inducedAmbientUltraweakEquiv N
  exact
    { toFun := fun T ↦
        ⟨(e T.1).1,
          ⟨Ultraweak.mem_ofSubmodule N.toSubmodule (e T.1).1 |>.mp (e T.1).2,
            by
              have hT := T.2
              change ‖((show N from T.1) : BH)‖ ≤ r at hT
              simpa only [e, IsUltraweakClosed.inducedAmbientUltraweakEquiv_apply,
                ofUltraweak_toUltraweak] using hT⟩⟩
      invFun := fun T ↦
        let Tsub : Ultraweak.ofSubmodule (P := BHPredual) N.toSubmodule :=
          ⟨T.1, Ultraweak.mem_ofSubmodule N.toSubmodule T.1 |>.mpr T.2.1⟩
        ⟨e.symm Tsub, by
          change ‖((show N from e.symm Tsub) : BH)‖ ≤ r
          have he := IsUltraweakClosed.inducedAmbientUltraweakEquiv_symm_apply N hN Tsub
          have hnorm := congrArg (fun x : N ↦ ‖(x : BH)‖) he
          rw [hnorm]
          exact T.2.2⟩
      left_inv := fun T ↦ by
        apply Subtype.ext
        exact e.symm_apply_apply T.1
      right_inv := fun T ↦ by
        apply Subtype.ext
        change (e (e.symm ⟨T.1, _⟩)).1 = T.1
        rw [e.apply_symm_apply]
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact continuous_subtype_val.comp (e.continuous.comp continuous_subtype_val)
      continuous_invFun := by
        have hsub : Continuous (fun T : AmbientUltraweakClosedBall (N : Set BH) r ↦
            (⟨T.1, Ultraweak.mem_ofSubmodule N.toSubmodule T.1 |>.mpr T.2.1⟩ :
              Ultraweak.ofSubmodule (P := BHPredual) N.toSubmodule)) := by
          apply Continuous.subtype_mk
          exact continuous_subtype_val
        apply Continuous.subtype_mk
        exact e.symm.continuous.comp hsub }

@[simp]
theorem IsUltraweakClosed.inducedAmbientUltraweakClosedBallHomeomorph_apply
    (N : NonUnitalStarSubalgebra ℂ BH)
    (hN : N.IsUltraweakClosed (P := BHPredual)) (r : ℝ)
    (T : InducedUltraweakClosedBall N hN r) :
    ofUltraweak (hN.inducedAmbientUltraweakClosedBallHomeomorph N r T).1 =
      ((show N from T.1) : BH) :=
  rfl

@[simp]
theorem IsUltraweakClosed.inducedAmbientUltraweakClosedBallHomeomorph_symm_apply
    (N : NonUnitalStarSubalgebra ℂ BH)
    (hN : N.IsUltraweakClosed (P := BHPredual)) (r : ℝ)
    (T : AmbientUltraweakClosedBall (N : Set BH) r) :
    ((show N from ((hN.inducedAmbientUltraweakClosedBallHomeomorph N r).symm T).1) : BH) =
      ofUltraweak T.1 :=
  rfl

/-- Sakai, Proposition 1.15.2(1): on every closed norm ball in a WOT-closed self-adjoint
operator algebra, the intrinsic weak-star topology `sigma(N, N_*)` agrees with Sakai's
coefficient-series sigma-WOT. -/
def IsWOTClosed.inducedUltraweakSigmaWOTClosedBallHomeomorph
    {N : NonUnitalStarSubalgebra ℂ BH} (hN : N.IsWOTClosed) (r : ℝ) :
    InducedUltraweakClosedBall N hN.isUltraweakClosed r ≃ₜ
      SigmaWOTClosedBall (N : Set BH) r :=
  (hN.isUltraweakClosed.inducedAmbientUltraweakClosedBallHomeomorph N r).trans
    (hN.isUltraweakClosed.ambientUltraweakSigmaWOTClosedBallHomeomorph N r)

/-- Sakai, Proposition 1.15.2(1): on every closed norm ball in a WOT-closed self-adjoint
operator algebra, the intrinsic weak-star topology `sigma(N, N_*)` agrees with WOT. -/
def IsWOTClosed.inducedUltraweakWOTClosedBallHomeomorph
    {N : NonUnitalStarSubalgebra ℂ BH} (hN : N.IsWOTClosed) (r : ℝ) :
    InducedUltraweakClosedBall N hN.isUltraweakClosed r ≃ₜ WOTClosedBall (N : Set BH) r :=
  (hN.isUltraweakClosed.inducedAmbientUltraweakClosedBallHomeomorph N r).trans
    (hN.isUltraweakClosed.ambientUltraweakWOTClosedBallHomeomorph N r)

@[simp]
theorem IsWOTClosed.inducedUltraweakSigmaWOTClosedBallHomeomorph_apply
    {N : NonUnitalStarSubalgebra ℂ BH} (hN : N.IsWOTClosed) (r : ℝ)
    (T : InducedUltraweakClosedBall N hN.isUltraweakClosed r) :
    ((hN.inducedUltraweakSigmaWOTClosedBallHomeomorph r T).1 : BH) =
      ((show N from T.1) : BH) :=
  rfl

@[simp]
theorem IsWOTClosed.inducedUltraweakSigmaWOTClosedBallHomeomorph_symm_apply
    {N : NonUnitalStarSubalgebra ℂ BH} (hN : N.IsWOTClosed) (r : ℝ)
    (T : SigmaWOTClosedBall (N : Set BH) r) :
    ((show N from ((hN.inducedUltraweakSigmaWOTClosedBallHomeomorph r).symm T).1) : BH) =
      (T.1 : BH) :=
  rfl

@[simp]
theorem IsWOTClosed.inducedUltraweakWOTClosedBallHomeomorph_apply
    {N : NonUnitalStarSubalgebra ℂ BH} (hN : N.IsWOTClosed) (r : ℝ)
    (T : InducedUltraweakClosedBall N hN.isUltraweakClosed r) :
    (hN.inducedUltraweakWOTClosedBallHomeomorph r T).1.toCLM =
      ((show N from T.1) : BH) :=
  rfl

@[simp]
theorem IsWOTClosed.inducedUltraweakWOTClosedBallHomeomorph_symm_apply
    {N : NonUnitalStarSubalgebra ℂ BH} (hN : N.IsWOTClosed) (r : ℝ)
    (T : WOTClosedBall (N : Set BH) r) :
    ((show N from ((hN.inducedUltraweakWOTClosedBallHomeomorph r).symm T).1) : BH) =
      T.1.toCLM :=
  rfl

/-- Arbitrary-filter form of the intrinsic sigma-WOT closed-ball equivalence in Sakai,
Proposition 1.15.2(1). -/
theorem IsWOTClosed.tendsto_sigmaWOT_iff_inducedUltraweak
    {N : NonUnitalStarSubalgebra ℂ BH} (hN : N.IsWOTClosed) (r : ℝ)
    {I : Type*} {l : Filter I}
    (f : I → InducedUltraweakClosedBall N hN.isUltraweakClosed r)
    (x : InducedUltraweakClosedBall N hN.isUltraweakClosed r) :
    Tendsto ((hN.inducedUltraweakSigmaWOTClosedBallHomeomorph r) ∘ f) l
        (nhds (hN.inducedUltraweakSigmaWOTClosedBallHomeomorph r x)) ↔
      Tendsto f l (nhds x) :=
  (hN.inducedUltraweakSigmaWOTClosedBallHomeomorph r).isInducing.tendsto_nhds_iff.symm

/-- Arbitrary-filter form of the intrinsic WOT closed-ball equivalence in Sakai,
Proposition 1.15.2(1). -/
theorem IsWOTClosed.tendsto_wot_iff_inducedUltraweak
    {N : NonUnitalStarSubalgebra ℂ BH} (hN : N.IsWOTClosed) (r : ℝ)
    {I : Type*} {l : Filter I}
    (f : I → InducedUltraweakClosedBall N hN.isUltraweakClosed r)
    (x : InducedUltraweakClosedBall N hN.isUltraweakClosed r) :
    Tendsto ((hN.inducedUltraweakWOTClosedBallHomeomorph r) ∘ f) l
        (nhds (hN.inducedUltraweakWOTClosedBallHomeomorph r x)) ↔
      Tendsto f l (nhds x) :=
  (hN.inducedUltraweakWOTClosedBallHomeomorph r).isInducing.tendsto_nhds_iff.symm

end NonUnitalStarSubalgebra
