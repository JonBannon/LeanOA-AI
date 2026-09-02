module

public import LeanOA.Ultraweak.BoundedOperatorStrongTopology

/-!
# Bounded operator-topology agreement

This file packages Sakai, Proposition 1.15.2 in its exact two-clause source order. For a
WOT-closed, possibly nonunital self-adjoint subalgebra `N` of `B(H)`, the package records

1. `WOT ≃ sigma-WOT ≃ sigma(N, N_*)`, and
2. `SOT ≃ ultrastrong ≃ s(N, N_*)`

on every zero-centered norm-closed ball. The fields are canonical identity homeomorphisms between
the topology-bearing closed-ball carriers. Consequently the package represents equality of the
restricted topologies without asserting any global equality of the ambient topologies.
-/

@[expose] public section

open Set
open scoped InnerProductSpace Ultraweak

noncomputable section

namespace NonUnitalStarSubalgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "BH" => H →L[ℂ] H
local notation "BHPredual" => ContinuousLinearMap.VectorFunctionalPredual ℂ H H

/-- The canonical closed-ball topology agreements in the two clauses of Sakai, Proposition
1.15.2, with both clauses and their three topologies listed in source order. -/
structure OperatorTopologyClosedBallAgreement
    (N : NonUnitalStarSubalgebra ℂ BH) (hN : N.IsWOTClosed) (r : ℝ) where
  /-- Weak-family source order, first step: WOT agrees with coefficient-series sigma-WOT. -/
  wotSigmaWOT :
    BoundedOperatorTopology.WOTClosedBall (N : Set BH) r ≃ₜ
      BoundedOperatorTopology.SigmaWOTClosedBall (N : Set BH) r
  /-- Weak-family source order, second step: coefficient-series sigma-WOT agrees with the
  intrinsic quotient-predual weak-star topology. -/
  sigmaWOTInducedUltraweak :
    BoundedOperatorTopology.SigmaWOTClosedBall (N : Set BH) r ≃ₜ
      InducedUltraweakClosedBall N hN.isUltraweakClosed r
  /-- Strong-family source order, first step: SOT agrees with coefficient-series ultrastrong
  convergence. -/
  sotUSOT :
    BoundedOperatorTopology.SOTClosedBall (N : Set BH) r ≃ₜ
      BoundedOperatorTopology.USOTClosedBall (N : Set BH) r
  /-- Strong-family source order, second step: coefficient-series ultrastrong convergence agrees
  with the intrinsic quotient-predual strong topology. -/
  usotInducedStrong :
    BoundedOperatorTopology.USOTClosedBall (N : Set BH) r ≃ₜ
      InducedStrongClosedBall N hN.isUltraweakClosed r

/-- Sakai, Proposition 1.15.2: on every bounded closed ball of a WOT-closed self-adjoint
subalgebra of `B(H)`, the weak operator, coefficient-series sigma-weak, and intrinsic weak-star
topologies agree, and the strong operator, coefficient-series ultrastrong, and intrinsic strong
topologies agree. -/
def IsWOTClosed.operatorTopologyClosedBallAgreement
    {N : NonUnitalStarSubalgebra ℂ BH} (hN : N.IsWOTClosed) (r : ℝ) :
    OperatorTopologyClosedBallAgreement N hN r where
  wotSigmaWOT :=
    (hN.isUltraweakClosed.sigmaWOTWOTClosedBallHomeomorph N r).symm
  sigmaWOTInducedUltraweak :=
    (hN.inducedUltraweakSigmaWOTClosedBallHomeomorph r).symm
  sotUSOT :=
    (hN.isUltraweakClosed.usotSOTClosedBallHomeomorph r).symm
  usotInducedStrong :=
    (hN.isUltraweakClosed.inducedStrongUSOTClosedBallHomeomorph r).symm

end NonUnitalStarSubalgebra
