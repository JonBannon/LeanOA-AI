import LeanOA.Ultraweak.ProjectionDecomposition

/-!
# Scratch test: the Radon--Stieltjes refinement bridge in Sakai 1.11.3

This file gives an explicit, proposition-level bridge from the three analytic inputs left implicit
by one explicit ultraweak candidate reading of Sakai's notation `a = ∫ λ de(λ)`:

* left-endpoint identity moment sums converge ultraweakly to `a`;
* their left and right endpoint projections converge ultraweakly to `0` and `1`;
* a map from a prescribed-cut subsystem is cofinal for the source division filter.

The bridge proves, rather than assumes, convergence of the translated sums to `r • 1 - a`.  It
also proves convergence of the varying left-residual lower bounds used in the support argument.
It deliberately defines no division, resolution, PVM, or integral object.  In particular, the
choice of a division filter remains visible as an input. A later source audit established that
Sakai's literal topology is strong and his division semantics are LEVEL C ambiguous.
-/

open Finset Filter
open scoped BigOperators Topology Ultraweak

namespace Scratch.SakaiRadonStieltjesBridge

section FiniteAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- The increment of an unbundled lower family on the half-open band `[q, t)`. -/
def band (e : ℝ → A) (q t : ℝ) : A :=
  e t - e q

/-- The left-endpoint identity moment sum on the first `n` bands.  This fixes the convention
needed to interpret the source's abstract Radon--Stieltjes notation. -/
noncomputable def identityMomentSum (e : ℝ → A) (cut : ℕ → ℝ) (n : ℕ) : A :=
  ∑ i ∈ range n, cut i • band e (cut i) (cut (i + 1))

/-- The left-endpoint moment sum translated by a real cut `r`. -/
noncomputable def translatedMomentSum
    (e : ℝ → A) (r : ℝ) (cut : ℕ → ℝ) (n : ℕ) : A :=
  ∑ i ∈ range n, (r - cut i) • band e (cut i) (cut (i + 1))

/-- Translation is a finite algebra identity.  No topology, positivity, projection law, or exact
endpoint is used: the endpoint defect remains explicitly
`r • (e (cut n) - e (cut 0))`. -/
theorem translatedMomentSum_eq_smul_endpoint_sub_identity
    (e : ℝ → A) (r : ℝ) (cut : ℕ → ℝ) (n : ℕ) :
    translatedMomentSum e r cut n =
      r • (e (cut n) - e (cut 0)) - identityMomentSum e cut n := by
  rw [translatedMomentSum, identityMomentSum]
  calc
    ∑ i ∈ range n, (r - cut i) • band e (cut i) (cut (i + 1)) =
        ∑ i ∈ range n,
          (r • band e (cut i) (cut (i + 1)) -
            cut i • band e (cut i) (cut (i + 1))) := by
      apply sum_congr rfl
      intro i hi
      rw [sub_smul]
    _ = (∑ i ∈ range n, r • band e (cut i) (cut (i + 1))) -
        ∑ i ∈ range n, cut i • band e (cut i) (cut (i + 1)) := by
      rw [sum_sub_distrib]
    _ = r • (∑ i ∈ range n, band e (cut i) (cut (i + 1))) -
        ∑ i ∈ range n, cut i • band e (cut i) (cut (i + 1)) := by
      rw [Finset.smul_sum]
    _ = r • (e (cut n) - e (cut 0)) -
        ∑ i ∈ range n, cut i • band e (cut i) (cut (i + 1)) := by
      rw [show ∑ i ∈ range n, band e (cut i) (cut (i + 1)) =
          e (cut n) - e (cut 0) by
        simpa only [band] using (Finset.sum_range_sub (fun i ↦ e (cut i)) n)]

end FiniteAlgebra

section UltraweakBridge

variable {M P D J : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]

/-- Cofinal restriction transports the identity-moment and unweighted-band limits and hence
forces the translated moment limit.  This is the smallest analytic signature for the translation
step itself. -/
theorem tendsto_translatedMomentSum_of_cofinal
    {lD : Filter D} {lJ : Filter J}
    (e : ℝ → M) (a : M) (cut : D → ℕ → ℝ) (bands : D → ℕ)
    (refine : J → D) (hrefine : Tendsto refine lJ lD) (r : ℝ)
    (hmoment : Tendsto
      (fun d ↦ toUltraweak ℂ P (identityMomentSum e (cut d) (bands d))) lD
      (nhds (toUltraweak ℂ P a)))
    (hband : Tendsto
      (fun d ↦ toUltraweak ℂ P (e (cut d (bands d)) - e (cut d 0))) lD
      (nhds (toUltraweak ℂ P 1))) :
    Tendsto
      (fun j ↦ toUltraweak ℂ P
        (translatedMomentSum e r (cut (refine j)) (bands (refine j)))) lJ
      (nhds (toUltraweak ℂ P (r • (1 : M) - a))) := by
  have hscaled : Tendsto
      (fun j ↦ toUltraweak ℂ P
        (r • (e (cut (refine j) (bands (refine j))) - e (cut (refine j) 0)))) lJ
      (nhds (toUltraweak ℂ P (r • (1 : M)))) := by
    simpa only [Function.comp_apply, Algebra.smul_def, Ultraweak.toUltraweak_mul] using
      (hband.comp hrefine).const_mul (toUltraweak ℂ P (algebraMap ℝ M r))
  have htranslated := hscaled.sub (hmoment.comp hrefine)
  simpa only [Function.comp_apply, translatedMomentSum_eq_smul_endpoint_sub_identity,
    toUltraweak_sub] using htranslated

/-- Cofinal restriction transports the identity-moment and endpoint limits and hence forces the
translated moment limit.  The map `refine` is intended to be the inclusion of divisions carrying
prescribed cuts (in the uniqueness proof, at least `r` and then `s < r`).

This theorem is the exact analytic bridge needed by the already checked finite below/above split.
It does not assert that a particular division model expresses Sakai's integral; that is the one
remaining source-semantics choice. -/
theorem tendsto_translatedMomentSum_of_cofinal_of_endpoint_limits
    {lD : Filter D} {lJ : Filter J}
    (e : ℝ → M) (a : M) (cut : D → ℕ → ℝ) (bands : D → ℕ)
    (refine : J → D) (hrefine : Tendsto refine lJ lD) (r : ℝ)
    (hmoment : Tendsto
      (fun d ↦ toUltraweak ℂ P (identityMomentSum e (cut d) (bands d))) lD
      (nhds (toUltraweak ℂ P a)))
    (hleft : Tendsto (fun d ↦ toUltraweak ℂ P (e (cut d 0))) lD
      (nhds (toUltraweak ℂ P 0)))
    (hright : Tendsto (fun d ↦ toUltraweak ℂ P (e (cut d (bands d)))) lD
      (nhds (toUltraweak ℂ P 1))) :
    Tendsto
      (fun j ↦ toUltraweak ℂ P
        (translatedMomentSum e r (cut (refine j)) (bands (refine j)))) lJ
      (nhds (toUltraweak ℂ P (r • (1 : M) - a))) := by
  apply tendsto_translatedMomentSum_of_cofinal (P := P)
    e a cut bands refine hrefine r hmoment
  simpa only [toUltraweak_sub, toUltraweak_zero, sub_zero] using hright.sub hleft

/-- A cofinal prescribed-cut restriction preserves vanishing of the left endpoint projection,
including after multiplication by any fixed real scalar. -/
theorem tendsto_leftEndpointResidual_of_cofinal
    {lD : Filter D} {lJ : Filter J}
    (e : ℝ → M) (cut : D → ℕ → ℝ) (refine : J → D)
    (hrefine : Tendsto refine lJ lD)
    (hleft : Tendsto (fun d ↦ toUltraweak ℂ P (e (cut d 0))) lD
      (nhds (toUltraweak ℂ P 0))) (c : ℝ) :
    Tendsto (fun j ↦ toUltraweak ℂ P (c • e (cut (refine j) 0))) lJ
      (nhds (toUltraweak ℂ P 0)) := by
  simpa only [Function.comp_apply, Algebra.smul_def, Ultraweak.toUltraweak_mul,
    toUltraweak_zero, mul_zero] using
    (hleft.comp hrefine).const_mul (toUltraweak ℂ P (algebraMap ℝ M c))

/-- Source-faithful varying lower comparison.  If a finite below-cut sum dominates the displayed
left side, closedness of order may pass this inequality to the limit.  Unlike an exact-endpoint
shortcut, the residual projection `e (cut _ 0)` is present at every finite stage and only vanishes
ultraweakly. -/
theorem tendsto_projection_sub_leftEndpointResidual_of_cofinal
    {lD : Filter D} {lJ : Filter J}
    (e : ℝ → M) (cut : D → ℕ → ℝ) (refine : J → D)
    (hrefine : Tendsto refine lJ lD)
    (hleft : Tendsto (fun d ↦ toUltraweak ℂ P (e (cut d 0))) lD
      (nhds (toUltraweak ℂ P 0))) (r s : ℝ) :
    Tendsto
      (fun j ↦ toUltraweak ℂ P
        ((r - s) • e s - (r - s) • e (cut (refine j) 0))) lJ
      (nhds (toUltraweak ℂ P ((r - s) • e s))) := by
  have hresidual := tendsto_leftEndpointResidual_of_cofinal
    (P := P) e cut refine hrefine hleft (r - s)
  simpa only [toUltraweak_sub, toUltraweak_zero, sub_zero] using
    (tendsto_const_nhds.sub hresidual : Tendsto
      (fun j ↦ toUltraweak ℂ P ((r - s) • e s) -
        toUltraweak ℂ P ((r - s) • e (cut (refine j) 0))) lJ
      (nhds (toUltraweak ℂ P ((r - s) • e s) - toUltraweak ℂ P 0)))

/-- The two analytic outputs required by the conditional support proof, packaged with explicit
ultraweak candidate assumptions. Prescribed-cut position equations are deliberately not hypotheses
here: they belong to the finite positivity/localization layer, while this theorem records only
what cofinality and the assumed moment/endpoint limits imply. -/
theorem tendsto_translated_and_lowerResidual_of_cofinal
    {lD : Filter D} {lJ : Filter J}
    (e : ℝ → M) (a : M) (cut : D → ℕ → ℝ) (bands : D → ℕ)
    (refine : J → D) (hrefine : Tendsto refine lJ lD) (r s : ℝ)
    (hmoment : Tendsto
      (fun d ↦ toUltraweak ℂ P (identityMomentSum e (cut d) (bands d))) lD
      (nhds (toUltraweak ℂ P a)))
    (hleft : Tendsto (fun d ↦ toUltraweak ℂ P (e (cut d 0))) lD
      (nhds (toUltraweak ℂ P 0)))
    (hright : Tendsto (fun d ↦ toUltraweak ℂ P (e (cut d (bands d)))) lD
      (nhds (toUltraweak ℂ P 1))) :
    Tendsto
        (fun j ↦ toUltraweak ℂ P
          (translatedMomentSum e r (cut (refine j)) (bands (refine j)))) lJ
        (nhds (toUltraweak ℂ P (r • (1 : M) - a))) ∧
      Tendsto
        (fun j ↦ toUltraweak ℂ P
          ((r - s) • e s - (r - s) • e (cut (refine j) 0))) lJ
        (nhds (toUltraweak ℂ P ((r - s) • e s))) := by
  exact ⟨tendsto_translatedMomentSum_of_cofinal_of_endpoint_limits
      (P := P) e a cut bands refine hrefine r hmoment hleft hright,
    tendsto_projection_sub_leftEndpointResidual_of_cofinal
      (P := P) e cut refine hrefine hleft r s⟩

/-- Ultraweak-candidate endpoint formulation. The competing family has ultraweak limits `0` and `1`
at `-∞` and `+∞`, while the chosen divisions have endpoints escaping in the corresponding
directions.  Composition derives the endpoint-projection nets used by the smaller bridge above.

This keeps separate a topology-forgotten consequence of the source's family-level endpoint clause
and the division system's endpoint escape condition; neither exact finite endpoint projection is
assumed. It does not identify the division system with Sakai's undefined integral. -/
theorem tendsto_translated_and_lowerResidual_of_cofinal_of_endpoint_escape
    {lD : Filter D} {lJ : Filter J}
    (e : ℝ → M) (a : M) (cut : D → ℕ → ℝ) (bands : D → ℕ)
    (refine : J → D) (hrefine : Tendsto refine lJ lD) (r s : ℝ)
    (hmoment : Tendsto
      (fun d ↦ toUltraweak ℂ P (identityMomentSum e (cut d) (bands d))) lD
      (nhds (toUltraweak ℂ P a)))
    (hcutLeft : Tendsto (fun d ↦ cut d 0) lD atBot)
    (hcutRight : Tendsto (fun d ↦ cut d (bands d)) lD atTop)
    (heAtBot : Tendsto (fun t ↦ toUltraweak ℂ P (e t)) atBot
      (nhds (toUltraweak ℂ P 0)))
    (heAtTop : Tendsto (fun t ↦ toUltraweak ℂ P (e t)) atTop
      (nhds (toUltraweak ℂ P 1))) :
    Tendsto
        (fun j ↦ toUltraweak ℂ P
          (translatedMomentSum e r (cut (refine j)) (bands (refine j)))) lJ
        (nhds (toUltraweak ℂ P (r • (1 : M) - a))) ∧
      Tendsto
        (fun j ↦ toUltraweak ℂ P
          ((r - s) • e s - (r - s) • e (cut (refine j) 0))) lJ
        (nhds (toUltraweak ℂ P ((r - s) • e s))) := by
  exact tendsto_translated_and_lowerResidual_of_cofinal
    (P := P) e a cut bands refine hrefine r s hmoment
      (heAtBot.comp hcutLeft) (heAtTop.comp hcutRight)

end UltraweakBridge

end Scratch.SakaiRadonStieltjesBridge
