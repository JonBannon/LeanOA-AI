import Scratch.FiniteCutEnumeration
import Scratch.RadonStieltjesMeshFilter
import Scratch.SakaiRadonStieltjesBridge
import Scratch.SakaiUniquenessFinite
import Scratch.CompetingSupportRecovery

/-!
# Scratch: a finite-set candidate semantics for Sakai's Radon--Stieltjes argument

**Statement-status warning:** this file tests one explicit candidate interpretation of Sakai's
Radon--Stieltjes hypothesis.  It does not claim that the candidate is source-equivalent to Sakai's
notation.  The additional hypothesis below says directly that left-endpoint identity moments over
all finite real cut sets, ordered by inclusion, converge ultraweakly to the represented element.

No definition or theorem in this file is proposed for production.  The purpose is to check that,
once this candidate moment semantics is assumed, the existing cofinality, finite splitting, and
support-recovery scratch layers compose without another analytic assumption.
-/

open Finset Filter Set
open scoped BigOperators Topology Ultraweak

namespace Scratch.SakaiRadonStieltjesFinsetCandidate

open Scratch.FiniteCutEnumeration

/-- The canonical index of `x` when it belongs to `d`, and zero otherwise.  Only the membership
case has mathematical meaning. -/
noncomputable def canonicalIndex (d : Finset ℝ) (x : ℝ) : ℕ :=
  if hx : x ∈ d then ((d.orderIsoOfFin rfl).symm ⟨x, hx⟩).1 else 0

theorem canonicalIndex_lt_card {d : Finset ℝ} {x : ℝ} (hx : x ∈ d) :
    canonicalIndex d x < d.card := by
  simp only [canonicalIndex, dif_pos hx]
  exact ((d.orderIsoOfFin rfl).symm ⟨x, hx⟩).2

theorem orderedCut_canonicalIndex {d : Finset ℝ} {x : ℝ} (hx : x ∈ d) :
    orderedCut d (canonicalIndex d x) = x := by
  rw [canonicalIndex, dif_pos hx]
  rw [orderedCut_of_lt_card d ((d.orderIsoOfFin rfl).symm ⟨x, hx⟩).2]
  change ↑(d.orderIsoOfFin rfl ((d.orderIsoOfFin rfl).symm ⟨x, hx⟩)) = x
  exact congrArg Subtype.val ((d.orderIsoOfFin rfl).apply_symm_apply ⟨x, hx⟩)

theorem canonicalIndex_le_bandCount {d : Finset ℝ} {x : ℝ} (hx : x ∈ d) :
    canonicalIndex d x ≤ bandCount d := by
  have hlt := canonicalIndex_lt_card hx
  rw [bandCount]
  omega

theorem canonicalIndex_mono {d : Finset ℝ} {x y : ℝ}
    (hx : x ∈ d) (hy : y ∈ d) (hxy : x ≤ y) :
    canonicalIndex d x ≤ canonicalIndex d y := by
  simp only [canonicalIndex, dif_pos hx, dif_pos hy]
  exact (d.orderIsoOfFin rfl).symm.monotone hxy

/-- Insert a fixed finite set of prescribed cuts. -/
noncomputable def addCuts (c d : Finset ℝ) : Finset ℝ := d ∪ c

/-- On any source filter that genuinely refines toward `atTop`, insertion of fixed cuts is
eventually the identity. -/
theorem eventuallyEq_addCuts_of_tendsto_atTop (c : Finset ℝ)
    {source : Filter (Finset ℝ)} (hsource : Tendsto id source atTop) :
    addCuts c =ᶠ[source] id := by
  filter_upwards [hsource.eventually (Filter.eventually_finset_atTop_subset c)] with d hd
  exact Finset.union_eq_left.mpr hd

/-- Hence insertion of fixed cuts is an endomap of every such richer source filter. -/
theorem tendsto_addCuts_self_of_tendsto_atTop (c : Finset ℝ)
    {source : Filter (Finset ℝ)} (hsource : Tendsto id source atTop) :
    Tendsto (addCuts c) source source :=
  tendsto_id.congr' (eventuallyEq_addCuts_of_tendsto_atTop c hsource).symm

section Bridge

variable {M P : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]

/-- Candidate-semantics specialization of the abstract Radon--Stieltjes bridge to finite real cut
sets and to the cofinal subsystem containing prescribed cuts `c`.

The only integral-like input is `hmoment`; endpoint projection convergence is derived by composing
the family endpoint laws with the kernel-checked escape of the minimum and maximum finite cuts. -/
theorem tendsto_translated_and_lowerResidual_finset_Ici
    (e : ℝ → M) (a : M) (c : Finset ℝ) (r s : ℝ)
    (hmoment : Tendsto
      (fun d : Finset ℝ ↦ toUltraweak ℂ P
        (Scratch.SakaiRadonStieltjesBridge.identityMomentSum e
          (orderedCut d) (bandCount d)))
      atTop (nhds (toUltraweak ℂ P a)))
    (heAtBot : Tendsto (fun t ↦ toUltraweak ℂ P (e t)) atBot
      (nhds (toUltraweak ℂ P 0)))
    (heAtTop : Tendsto (fun t ↦ toUltraweak ℂ P (e t)) atTop
      (nhds (toUltraweak ℂ P 1))) :
    Tendsto
        (fun d : Ici c ↦ toUltraweak ℂ P
          (Scratch.SakaiRadonStieltjesBridge.translatedMomentSum e r
            (orderedCut d.1) (bandCount d.1)))
        atTop (nhds (toUltraweak ℂ P (r • (1 : M) - a))) ∧
      Tendsto
        (fun d : Ici c ↦ toUltraweak ℂ P
          ((r - s) • e s - (r - s) • e (orderedCut d.1 0)))
        atTop (nhds (toUltraweak ℂ P ((r - s) • e s))) := by
  apply Scratch.SakaiRadonStieltjesBridge.tendsto_translated_and_lowerResidual_of_cofinal_of_endpoint_escape
      (P := P) e a orderedCut bandCount ((↑) : Ici c → Finset ℝ)
      (Filter.map_val_Ici_atTop c).le r s hmoment
      tendsto_leftEndpoint_atBot tendsto_rightEndpoint_atTop heAtBot heAtTop

end Bridge

section CandidateUniqueness

open Scratch.SakaiUniquenessFinite
open Scratch.CompetingSupportRecovery
open WStarAlgebra

variable {M P : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]
  [WStarAlgebra M]

/-- The finite positive piece below the prescribed cut `r`. -/
noncomputable def belowNet
    (e : ℝ → StarProjection M) (r : ℝ) (d : Finset ℝ) : M :=
  belowTranslatedSum e r (orderedCut (addCuts {r} d))
    (canonicalIndex (addCuts {r} d) r)

/-- The magnitude of the finite negative piece above the prescribed cut `r`. -/
noncomputable def aboveNet
    (e : ℝ → StarProjection M) (r : ℝ) (d : Finset ℝ) : M :=
  aboveTranslatedMagnitude e r (orderedCut (addCuts {r} d))
    (canonicalIndex (addCuts {r} d) r)
    (bandCount (addCuts {r} d) - canonicalIndex (addCuts {r} d) r)

/-- The source-faithful lower comparison, evaluated after prescribing both `s` and `r`. -/
noncomputable def lowerNet
    (e : ℝ → StarProjection M) (r s : ℝ) (d : Finset ℝ) : M :=
  (r - s) • (e s).1 -
    (r - s) • (e (orderedCut (addCuts {s, r} d) 0)).1

private theorem mem_addCuts_right (c d : Finset ℝ) {x : ℝ} (hx : x ∈ c) :
    x ∈ addCuts c d := by
  exact Finset.mem_union_right d hx

omit [PartialOrder M] [StarOrderedRing M] [WStarAlgebra M] in
private theorem bridge_translated_eq_finite
    (e : ℝ → StarProjection M) (r : ℝ) (cut : ℕ → ℝ) (n : ℕ) :
    Scratch.SakaiRadonStieltjesBridge.translatedMomentSum
        (fun t ↦ (e t).1) r cut n =
      Scratch.SakaiUniquenessFinite.translatedMomentSum e r cut n :=
  rfl

/-- **Candidate semantics, not source equivalence.**

Assume explicitly that the left-endpoint identity moments indexed by an arbitrary richer source
filter converge to `a`, and that this source still tends to finite-cut refinement `atTop`. Then the
finite split and support-recovery layers identify the competing family at the cut `r`.

The source filter may retain mesh, endpoint, or other cut-set-dependent admissibility data.
Independent tags would require a richer index type with a projection to `Finset ℝ`. Prescribing
`{r}` and `{s,r}` by finite union is eventually the identity and therefore does not alter any of
the cut-set conditions. -/
theorem competing_eq_spectralProjectionIio_of_finset_candidate
    {source : Filter (Finset ℝ)} [NeBot source]
    (hsource : Tendsto id source atTop)
    (e : ℝ → StarProjection M) (he : Monotone e)
    (hcont : ∀ (f : ℕ → ℝ) (t : ℝ), Monotone f → Tendsto f atTop (nhds t) →
      Tendsto (fun n ↦ toUltraweak ℂ P (e (f n)).1) atTop
        (nhds (toUltraweak ℂ P (e t).1)))
    (heAtBot : Tendsto (fun t ↦ toUltraweak ℂ P (e t).1) atBot
      (nhds (toUltraweak ℂ P 0)))
    (heAtTop : Tendsto (fun t ↦ toUltraweak ℂ P (e t).1) atTop
      (nhds (toUltraweak ℂ P 1)))
    (a : selfAdjoint M)
    (hmoment : Tendsto
      (fun d : Finset ℝ ↦ toUltraweak ℂ P
        (Scratch.SakaiRadonStieltjesBridge.identityMomentSum
          (fun t ↦ (e t).1) (orderedCut d) (bandCount d)))
      source (nhds (toUltraweak ℂ P a.1)))
    (r : ℝ) : e r = spectralProjectionIio a r := by
  let insertR : Finset ℝ → Finset ℝ := addCuts {r}
  have hrefineR : Tendsto insertR source source :=
    tendsto_addCuts_self_of_tendsto_atTop {r} hsource
  have hleft : Tendsto
      (fun d : Finset ℝ ↦ orderedCut d 0) source atBot :=
    tendsto_leftEndpoint_atBot.comp hsource
  have hright : Tendsto
      (fun d : Finset ℝ ↦ orderedCut d (bandCount d)) source atTop :=
    tendsto_rightEndpoint_atTop.comp hsource
  have htranslated : Tendsto
      (fun d : Finset ℝ ↦ toUltraweak ℂ P
        (Scratch.SakaiRadonStieltjesBridge.translatedMomentSum
          (fun t ↦ (e t).1) r (orderedCut (insertR d)) (bandCount (insertR d))))
      source (nhds (toUltraweak ℂ P (r • (1 : M) - a.1))) :=
    (Scratch.SakaiRadonStieltjesBridge.tendsto_translated_and_lowerResidual_of_cofinal_of_endpoint_escape
        (P := P) (fun t ↦ (e t).1) a.1 orderedCut bandCount insertR hrefineR r r
        hmoment hleft hright heAtBot heAtTop).1
  have hmomentSplit : Tendsto
      (fun d : Finset ℝ ↦ toUltraweak ℂ P (belowNet e r d - aboveNet e r d))
      source
      (nhds (toUltraweak ℂ P (algebraMap ℝ M r - a.1))) := by
    have hsame : ∀ d : Finset ℝ,
        belowNet e r d - aboveNet e r d =
          Scratch.SakaiRadonStieltjesBridge.translatedMomentSum
            (fun t ↦ (e t).1) r (orderedCut (insertR d)) (bandCount (insertR d)) := by
      intro d
      have hr : r ∈ insertR d := mem_addCuts_right {r} d (by simp)
      have hk : canonicalIndex (insertR d) r ≤ bandCount (insertR d) :=
        canonicalIndex_le_bandCount hr
      rw [bridge_translated_eq_finite e r]
      simpa only [belowNet, aboveNet, insertR, Nat.add_sub_of_le hk] using
        (Scratch.SakaiUniquenessFinite.translatedMomentSum_eq_below_sub_above
          e r (orderedCut (addCuts {r} d)) (canonicalIndex (addCuts {r} d) r)
          (bandCount (addCuts {r} d) - canonicalIndex (addCuts {r} d) r)).symm
    have hsplit := htranslated.congr' <| Eventually.of_forall fun d ↦
      congrArg (toUltraweak ℂ P) (hsame d).symm
    simpa only [Algebra.smul_def, mul_one] using hsplit
  have huNonneg : ∀ᶠ d in source, 0 ≤ belowNet e r d :=
    Eventually.of_forall fun d ↦ by
      have hr : r ∈ addCuts {r} d := mem_addCuts_right {r} d (by simp)
      exact belowTranslatedSum_nonneg e he r _ _
        (monotone_orderedCut _ ⟨r, hr⟩) (orderedCut_canonicalIndex hr)
  have hvNonneg : ∀ᶠ d in source, 0 ≤ aboveNet e r d :=
    Eventually.of_forall fun d ↦ by
      have hr : r ∈ addCuts {r} d := mem_addCuts_right {r} d (by simp)
      exact aboveTranslatedMagnitude_nonneg e he r _ _ _
        (monotone_orderedCut _ ⟨r, hr⟩) (orderedCut_canonicalIndex hr)
  have hpu : ∀ᶠ d in source, (e r).1 * belowNet e r d = belowNet e r d :=
    Eventually.of_forall fun d ↦ by
      have hr : r ∈ addCuts {r} d := mem_addCuts_right {r} d (by simp)
      exact mul_belowTranslatedSum_eq_self e he r _ _
        (monotone_orderedCut _ ⟨r, hr⟩) (orderedCut_canonicalIndex hr)
  have hpv : ∀ᶠ d in source, (e r).1 * aboveNet e r d = 0 :=
    Eventually.of_forall fun d ↦ by
      have hr : r ∈ addCuts {r} d := mem_addCuts_right {r} d (by simp)
      exact mul_aboveTranslatedMagnitude_eq_zero e he r _ _ _
        (monotone_orderedCut _ ⟨r, hr⟩) (orderedCut_canonicalIndex hr)
  apply competing_eq_spectralProjectionIio_of_continuousBelow
    (P := P) e he hcont a r hmomentSplit huNonneg hvNonneg hpu hpv
  · intro s hsr
    let insertSR : Finset ℝ → Finset ℝ := addCuts {s, r}
    have hrefineSR : Tendsto insertSR source source :=
      tendsto_addCuts_self_of_tendsto_atTop {s, r} hsource
    exact Scratch.SakaiRadonStieltjesBridge.tendsto_projection_sub_leftEndpointResidual_of_cofinal
        (P := P) (fun t ↦ (e t).1) orderedCut insertSR hrefineSR
        (heAtBot.comp hleft) r s
  · intro s hsr
    filter_upwards [hsource.eventually
      (Filter.eventually_finset_atTop_subset ({s, r} : Finset ℝ))] with d hd
    have hs : s ∈ d := hd (by simp)
    have hr : r ∈ d := hd (by simp)
    have hsub : ({s, r} : Finset ℝ) ⊆ d := hd
    have hrsub : ({r} : Finset ℝ) ⊆ d := by
      intro x hx
      rcases Finset.mem_singleton.mp hx with rfl
      exact hr
    simp only [belowNet]
    rw [show addCuts {s, r} d = d by exact Finset.union_eq_left.mpr hsub,
      show addCuts {r} d = d by exact Finset.union_eq_left.mpr hrsub]
    exact smul_projection_sub_residual_le_belowTranslatedSum
      e he r s (orderedCut d) (canonicalIndex_mono hs hr hsr.le)
      (monotone_orderedCut d ⟨r, hr⟩)
      (orderedCut_canonicalIndex hs) (orderedCut_canonicalIndex hr)

/-- Bare refinement `atTop` is the immediate concrete specialization of the filter-parametric
candidate theorem. -/
theorem competing_eq_spectralProjectionIio_of_finset_atTop_candidate
    (e : ℝ → StarProjection M) (he : Monotone e)
    (hcont : ∀ (f : ℕ → ℝ) (t : ℝ), Monotone f → Tendsto f atTop (nhds t) →
      Tendsto (fun n ↦ toUltraweak ℂ P (e (f n)).1) atTop
        (nhds (toUltraweak ℂ P (e t).1)))
    (heAtBot : Tendsto (fun t ↦ toUltraweak ℂ P (e t).1) atBot
      (nhds (toUltraweak ℂ P 0)))
    (heAtTop : Tendsto (fun t ↦ toUltraweak ℂ P (e t).1) atTop
      (nhds (toUltraweak ℂ P 1)))
    (a : selfAdjoint M)
    (hmoment : Tendsto
      (fun d : Finset ℝ ↦ toUltraweak ℂ P
        (Scratch.SakaiRadonStieltjesBridge.identityMomentSum
          (fun t ↦ (e t).1) (orderedCut d) (bandCount d)))
      atTop (nhds (toUltraweak ℂ P a.1)))
    (r : ℝ) : e r = spectralProjectionIio a r := by
  exact competing_eq_spectralProjectionIio_of_finset_candidate
    (P := P) tendsto_id e he hcont heAtBot heAtTop a hmoment r

/-- Concrete specialization to the kernel-checked filter combining inclusion refinement and
shrinking global mesh.  Endpoint escape follows from its refinement coordinate.  This is still a
candidate translation of Sakai's abstract integral, not a source-equivalence theorem. -/
theorem competing_eq_spectralProjectionIio_of_mesh_refinement_candidate
    (e : ℝ → StarProjection M) (he : Monotone e)
    (hcont : ∀ (f : ℕ → ℝ) (t : ℝ), Monotone f → Tendsto f atTop (nhds t) →
      Tendsto (fun n ↦ toUltraweak ℂ P (e (f n)).1) atTop
        (nhds (toUltraweak ℂ P (e t).1)))
    (heAtBot : Tendsto (fun t ↦ toUltraweak ℂ P (e t).1) atBot
      (nhds (toUltraweak ℂ P 0)))
    (heAtTop : Tendsto (fun t ↦ toUltraweak ℂ P (e t).1) atTop
      (nhds (toUltraweak ℂ P 1)))
    (a : selfAdjoint M)
    (hmoment : Tendsto
      (fun d : Finset ℝ ↦ toUltraweak ℂ P
        (Scratch.SakaiRadonStieltjesBridge.identityMomentSum
          (fun t ↦ (e t).1) (orderedCut d) (bandCount d)))
      Scratch.RadonStieltjesMeshFilter.stieltjesFilter
      (nhds (toUltraweak ℂ P a.1)))
    (r : ℝ) : e r = spectralProjectionIio a r := by
  letI : NeBot Scratch.RadonStieltjesMeshFilter.stieltjesFilter :=
    Scratch.RadonStieltjesMeshFilter.stieltjesFilter_neBot
  exact competing_eq_spectralProjectionIio_of_finset_candidate
    (P := P) Scratch.RadonStieltjesMeshFilter.tendsto_id_stieltjesFilter_atTop
    e he hcont heAtBot heAtTop a hmoment r

/-- Two competing families satisfying the explicit candidate semantics over the same richer
source filter coincide. This is family uniqueness conditional on the candidate, not a theorem
that Sakai's source notation has already been translated equivalently. -/
theorem competing_family_unique_of_finset_candidate
    {source source' : Filter (Finset ℝ)} [NeBot source] [NeBot source']
    (hsource : Tendsto id source atTop)
    (hsource' : Tendsto id source' atTop)
    (e e' : ℝ → StarProjection M) (he : Monotone e) (he' : Monotone e')
    (hcont : ∀ (f : ℕ → ℝ) (t : ℝ), Monotone f → Tendsto f atTop (nhds t) →
      Tendsto (fun n ↦ toUltraweak ℂ P (e (f n)).1) atTop
        (nhds (toUltraweak ℂ P (e t).1)))
    (hcont' : ∀ (f : ℕ → ℝ) (t : ℝ), Monotone f → Tendsto f atTop (nhds t) →
      Tendsto (fun n ↦ toUltraweak ℂ P (e' (f n)).1) atTop
        (nhds (toUltraweak ℂ P (e' t).1)))
    (heAtBot : Tendsto (fun t ↦ toUltraweak ℂ P (e t).1) atBot
      (nhds (toUltraweak ℂ P 0)))
    (heAtTop : Tendsto (fun t ↦ toUltraweak ℂ P (e t).1) atTop
      (nhds (toUltraweak ℂ P 1)))
    (heAtBot' : Tendsto (fun t ↦ toUltraweak ℂ P (e' t).1) atBot
      (nhds (toUltraweak ℂ P 0)))
    (heAtTop' : Tendsto (fun t ↦ toUltraweak ℂ P (e' t).1) atTop
      (nhds (toUltraweak ℂ P 1)))
    (a : selfAdjoint M)
    (hmoment : Tendsto
      (fun d : Finset ℝ ↦ toUltraweak ℂ P
        (Scratch.SakaiRadonStieltjesBridge.identityMomentSum
          (fun t ↦ (e t).1) (orderedCut d) (bandCount d)))
      source (nhds (toUltraweak ℂ P a.1)))
    (hmoment' : Tendsto
      (fun d : Finset ℝ ↦ toUltraweak ℂ P
        (Scratch.SakaiRadonStieltjesBridge.identityMomentSum
          (fun t ↦ (e' t).1) (orderedCut d) (bandCount d)))
      source' (nhds (toUltraweak ℂ P a.1))) : e = e' := by
  apply competing_family_unique_of_pointwise_recovery a
  · intro r
    exact competing_eq_spectralProjectionIio_of_finset_candidate
      (P := P) hsource e he hcont heAtBot heAtTop a hmoment r
  · intro r
    exact competing_eq_spectralProjectionIio_of_finset_candidate
      (P := P) hsource' e' he' hcont' heAtBot' heAtTop' a hmoment' r

/-- Two families satisfying the concrete refinement-plus-mesh candidate moment semantics agree.
The source-equivalence warning on the pointwise theorem remains in force. -/
theorem competing_family_unique_of_mesh_refinement_candidate
    (e e' : ℝ → StarProjection M) (he : Monotone e) (he' : Monotone e')
    (hcont : ∀ (f : ℕ → ℝ) (t : ℝ), Monotone f → Tendsto f atTop (nhds t) →
      Tendsto (fun n ↦ toUltraweak ℂ P (e (f n)).1) atTop
        (nhds (toUltraweak ℂ P (e t).1)))
    (hcont' : ∀ (f : ℕ → ℝ) (t : ℝ), Monotone f → Tendsto f atTop (nhds t) →
      Tendsto (fun n ↦ toUltraweak ℂ P (e' (f n)).1) atTop
        (nhds (toUltraweak ℂ P (e' t).1)))
    (heAtBot : Tendsto (fun t ↦ toUltraweak ℂ P (e t).1) atBot
      (nhds (toUltraweak ℂ P 0)))
    (heAtTop : Tendsto (fun t ↦ toUltraweak ℂ P (e t).1) atTop
      (nhds (toUltraweak ℂ P 1)))
    (heAtBot' : Tendsto (fun t ↦ toUltraweak ℂ P (e' t).1) atBot
      (nhds (toUltraweak ℂ P 0)))
    (heAtTop' : Tendsto (fun t ↦ toUltraweak ℂ P (e' t).1) atTop
      (nhds (toUltraweak ℂ P 1)))
    (a : selfAdjoint M)
    (hmoment : Tendsto
      (fun d : Finset ℝ ↦ toUltraweak ℂ P
        (Scratch.SakaiRadonStieltjesBridge.identityMomentSum
          (fun t ↦ (e t).1) (orderedCut d) (bandCount d)))
      Scratch.RadonStieltjesMeshFilter.stieltjesFilter
      (nhds (toUltraweak ℂ P a.1)))
    (hmoment' : Tendsto
      (fun d : Finset ℝ ↦ toUltraweak ℂ P
        (Scratch.SakaiRadonStieltjesBridge.identityMomentSum
          (fun t ↦ (e' t).1) (orderedCut d) (bandCount d)))
      Scratch.RadonStieltjesMeshFilter.stieltjesFilter
      (nhds (toUltraweak ℂ P a.1))) : e = e' := by
  letI : NeBot Scratch.RadonStieltjesMeshFilter.stieltjesFilter :=
    Scratch.RadonStieltjesMeshFilter.stieltjesFilter_neBot
  exact competing_family_unique_of_finset_candidate
    (P := P) Scratch.RadonStieltjesMeshFilter.tendsto_id_stieltjesFilter_atTop
    Scratch.RadonStieltjesMeshFilter.tendsto_id_stieltjesFilter_atTop
    e e' he he' hcont hcont' heAtBot heAtTop heAtBot' heAtTop' a hmoment hmoment'

end CandidateUniqueness

end Scratch.SakaiRadonStieltjesFinsetCandidate
