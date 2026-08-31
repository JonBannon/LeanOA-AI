import LeanOA.Ultraweak.Strong
import Scratch.SakaiRadonStieltjesFinsetCandidate

/-!
# Scratch: Sakai's strong topology versus the checked ultraweak candidate

Sakai, Theorem 1.11.3, printed page 26, states both continuity from below and the abstract
Radon--Stieltjes representation in the `s(M, M_*)` topology, not in the
`σ(M, M_*)` topology.  This file checks only the topology-forgetting step: if the exact same
finite-cut net converges in Sak-AI's specified strong topology, then it satisfies the ultraweak
hypotheses consumed by the already checked conditional uniqueness theorem.

This is not a source-semantics theorem.  It neither identifies Sakai's undefined integral with the
finite-cut net nor supplies his endpoint/improper-integral convention.
-/

open Filter
open scoped Topology Ultraweak

namespace Scratch.SakaiStrongRadonStieltjesBridge

variable {M P : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]

/-- Convergence in the specified strong topology implies convergence of the same net in the
specified ultraweak topology. -/
theorem tendsto_toUltraweak_of_tendsto_toStrong {ι : Type*} {l : Filter ι}
    {f : ι → M} {x : M}
    (h : Tendsto (fun i ↦ Ultraweak.toStrong P (f i)) l
      (nhds (Ultraweak.toStrong P x))) :
    Tendsto (fun i ↦ toUltraweak ℂ P (f i)) l
      (nhds (toUltraweak ℂ P x)) := by
  have hmap :=
    (Ultraweak.Strong.continuous_toUltraweakₗ (M := M) (P := P)).tendsto
      (Ultraweak.toStrong P x)
  have := hmap.comp h
  change Tendsto
    (fun i ↦ Ultraweak.Strong.toUltraweakₗ (Ultraweak.toStrong P (f i))) l
    (nhds (Ultraweak.Strong.toUltraweakₗ (Ultraweak.toStrong P x))) at this
  simpa [Ultraweak.Strong.toUltraweakₗ_apply, Ultraweak.toStrong, Ultraweak.ofStrong] using this

section Uniqueness

open Scratch.FiniteCutEnumeration
open Scratch.SakaiRadonStieltjesFinsetCandidate
open Scratch.SakaiUniquenessFinite
open WStarAlgebra

variable [WStarAlgebra M]

/-- Strong-topology version of the filter-parametric clarified uniqueness theorem.

The continuity and moment limits are assumed in Sakai's actual `s(M, M_*)` topology; the source's
unqualified endpoint arrows are made strong here as the coherent local choice. The theorem forgets
all of those limits to the ultraweak topology and invokes the previously checked finite-cut
uniqueness chain. The division semantics remain an explicit candidate, not a translation of
Sakai's phrase “abstract Radon--Stieltjes integral.” -/
theorem competing_eq_spectralProjectionIio_of_strong_finset_candidate
    {source : Filter (Finset ℝ)} [NeBot source]
    (hsource : Tendsto id source atTop)
    (e : ℝ → StarProjection M) (he : Monotone e)
    (hcont : ∀ (f : ℕ → ℝ) (t : ℝ), Monotone f → Tendsto f atTop (nhds t) →
      Tendsto (fun n ↦ Ultraweak.toStrong P (e (f n)).1) atTop
        (nhds (Ultraweak.toStrong P (e t).1)))
    (heAtBot : Tendsto (fun t ↦ Ultraweak.toStrong P (e t).1) atBot
      (nhds (Ultraweak.toStrong P 0)))
    (heAtTop : Tendsto (fun t ↦ Ultraweak.toStrong P (e t).1) atTop
      (nhds (Ultraweak.toStrong P 1)))
    (a : selfAdjoint M)
    (hmoment : Tendsto
      (fun d : Finset ℝ ↦ Ultraweak.toStrong P
        (Scratch.SakaiRadonStieltjesBridge.identityMomentSum
          (fun t ↦ (e t).1) (orderedCut d) (bandCount d)))
      source (nhds (Ultraweak.toStrong P a.1)))
    (r : ℝ) : e r = spectralProjectionIio a r := by
  apply competing_eq_spectralProjectionIio_of_finset_candidate
    (P := P) hsource e he
  · intro f t hf hft
    exact tendsto_toUltraweak_of_tendsto_toStrong (hcont f t hf hft)
  · exact tendsto_toUltraweak_of_tendsto_toStrong heAtBot
  · exact tendsto_toUltraweak_of_tendsto_toStrong heAtTop
  · exact tendsto_toUltraweak_of_tendsto_toStrong hmoment

end Uniqueness

end Scratch.SakaiStrongRadonStieltjesBridge
