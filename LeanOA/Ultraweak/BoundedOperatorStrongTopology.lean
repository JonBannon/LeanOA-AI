module

public import LeanOA.Ultraweak.BoundedOperatorTopology
public import LeanOA.Ultraweak.BoundedOperatorUltrastrong
public import LeanOA.Ultraweak.InducedStrong

/-!
# Strong operator topologies on norm-bounded sets

This file formalizes the strong-family half of Sakai, Proposition 1.15.2. For a WOT-closed,
possibly nonunital self-adjoint operator algebra `N`, the strong operator topology, Sakai's
coefficient-series ultrastrong topology, and the intrinsic strong topology determined by the
canonical quotient predual of `N` agree on every zero-centered norm-closed ball.

The public comparison theorems use ultraweak closedness, the semantic hypothesis needed to form
the quotient predual. For concrete self-adjoint subalgebras of `B(H)`, this is equivalent to the
WOT-closedness hypothesis in Sakai's statement.

The proof is filter-general. It sends convergence to weak convergence of the positive-square
errors `(xᵢ - x)⋆ * (xᵢ - x)` and invokes the bounded weak-family comparison from
`LeanOA.Ultraweak.BoundedOperatorTopology` on the resulting square ball. Thus the result does
not assert a global equality of the three topologies, use a trace-class representation theorem,
or weaken the source statement to sequences.
-/

@[expose] public section

open Metric Set Filter
open scoped ComplexOrder InnerProductSpace Ultraweak

noncomputable section

namespace BoundedOperatorTopology

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

local notation "EF" => E →L[𝕜] F

/-- The part of a closed norm ball carried by Mathlib's strong operator topology. -/
abbrev SOTClosedBall (s : Set EF) (r : ℝ) :=
  {T : E →Lₚₜ[𝕜] F // (show EF from T) ∈ s ∧ ‖(show EF from T)‖ ≤ r}

/-- The part of a closed norm ball carried by square-summable convergence. For Hilbert-space
endomorphisms this is the concrete ultrastrong operator topology. -/
abbrev USOTClosedBall (s : Set EF) (r : ℝ) :=
  {T : E →USOT[𝕜] F // T.toCLM ∈ s ∧ ‖T.toCLM‖ ≤ r}

/-- The carrier equivalence underlying the bounded ultrastrong/SOT comparison. -/
def usotSOTClosedBallEquiv (s : Set EF) (r : ℝ) :
    USOTClosedBall s r ≃ SOTClosedBall s r where
  toFun T := ⟨SquareSummableConvergenceCLM.toPointwiseConvergenceCLM T.1,
    T.2.1, T.2.2⟩
  invFun T := ⟨SquareSummableConvergenceCLM.ofCLM (show EF from T.1), T.2.1, T.2.2⟩
  left_inv T := by apply Subtype.ext; rfl
  right_inv T := by apply Subtype.ext; rfl

/-- The canonical identity from the square-summable-convergence closed-ball carrier to the
pointwise-convergence closed-ball carrier is continuous. -/
lemma continuous_usotSOTClosedBallEquiv (s : Set EF) (r : ℝ) :
    Continuous (usotSOTClosedBallEquiv s r) := by
  apply Continuous.subtype_mk
  exact SquareSummableConvergenceCLM.toPointwiseConvergenceCLM.continuous.comp
    continuous_subtype_val

end BoundedOperatorTopology

namespace NonUnitalStarSubalgebra

section BoundedOperators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "BH" => H →L[ℂ] H
local notation "BHPredual" => ContinuousLinearMap.VectorFunctionalPredual ℂ H H

/-- The carrier equivalence from the intrinsic strong closed ball to the concrete SOT closed
ball. Its topological content is established below under ultraweak closedness. -/
def IsUltraweakClosed.inducedStrongSOTClosedBallEquiv
    {N : NonUnitalStarSubalgebra ℂ BH}
    (hN : N.IsUltraweakClosed (P := BHPredual)) (r : ℝ) :
    InducedStrongClosedBall N hN r ≃
      BoundedOperatorTopology.SOTClosedBall (N : Set BH) r := by
  letI : NonUnitalCStarAlgebra N := hN.nonUnitalCStarAlgebra N
  letI : IsUnital N := hN.isUnital N
  letI : CStarAlgebra N := IsUnital.toCStarAlgebra
  letI : PartialOrder N := CStarAlgebra.spectralOrder N
  letI : StarOrderedRing N := CStarAlgebra.spectralOrderedRing N
  letI : Predual ℂ N (BHPredual ⧸
      Ultraweak.preannihilator (P := BHPredual) N.toSubmodule) :=
    hN.inducedPredual N
  exact
    { toFun := fun T ↦
        ⟨(show H →Lₚₜ[ℂ] H from ((show N from Ultraweak.ofStrong T.1) : BH)),
          (show N from Ultraweak.ofStrong T.1).property, T.2⟩
      invFun := fun T ↦
        ⟨Ultraweak.toStrong
            (BHPredual ⧸ Ultraweak.preannihilator (P := BHPredual) N.toSubmodule)
            (⟨(show BH from T.1), T.2.1⟩ : N), T.2.2⟩
      left_inv := fun T ↦ by apply Subtype.ext; rfl
      right_inv := fun T ↦ by apply Subtype.ext; rfl }

@[simp]
lemma IsUltraweakClosed.inducedStrongSOTClosedBallEquiv_apply
    {N : NonUnitalStarSubalgebra ℂ BH}
    (hN : N.IsUltraweakClosed (P := BHPredual)) (r : ℝ)
    (T : InducedStrongClosedBall N hN r) :
    (show BH from (hN.inducedStrongSOTClosedBallEquiv r T).1) =
      ((show N from T.1) : BH) :=
  rfl

@[simp]
lemma IsUltraweakClosed.inducedStrongSOTClosedBallEquiv_symm_apply
    {N : NonUnitalStarSubalgebra ℂ BH}
    (hN : N.IsUltraweakClosed (P := BHPredual)) (r : ℝ)
    (T : BoundedOperatorTopology.SOTClosedBall (N : Set BH) r) :
    ((show N from ((hN.inducedStrongSOTClosedBallEquiv r).symm T).1) : BH) =
      (show BH from T.1) :=
  rfl

/-- Positive-square errors from an intrinsic strong closed ball, regarded in the intrinsic
ultraweak square ball. -/
private def IsUltraweakClosed.inducedStrongSquare
    {N : NonUnitalStarSubalgebra ℂ BH}
    (hN : N.IsUltraweakClosed (P := BHPredual)) (r : ℝ)
    (x a : InducedStrongClosedBall N hN r) :
    InducedUltraweakClosedBall N hN ((2 * r) ^ 2) := by
  letI : NonUnitalCStarAlgebra N := hN.nonUnitalCStarAlgebra N
  letI : IsUnital N := hN.isUnital N
  letI : CStarAlgebra N := IsUnital.toCStarAlgebra
  letI : PartialOrder N := CStarAlgebra.spectralOrder N
  letI : StarOrderedRing N := CStarAlgebra.spectralOrderedRing N
  letI : Predual ℂ N (BHPredual ⧸
      Ultraweak.preannihilator (P := BHPredual) N.toSubmodule) :=
    hN.inducedPredual N
  exact ⟨toUltraweak ℂ
      (BHPredual ⧸ Ultraweak.preannihilator (P := BHPredual) N.toSubmodule)
      (star ((show N from Ultraweak.ofStrong a.1) -
        (show N from Ultraweak.ofStrong x.1)) *
        ((show N from Ultraweak.ofStrong a.1) -
        (show N from Ultraweak.ofStrong x.1))),
    by
      change ‖star ((show N from a.1) - (show N from x.1)) *
        ((show N from a.1) - (show N from x.1))‖ ≤ (2 * r) ^ 2
      simpa only [two_mul] using
        (CStarRing.norm_star_sub_mul_self_le_add_sq
          (R := N) (a := (show N from a.1)) (x := (show N from x.1)) a.2 x.2)⟩

/-- Positive-square errors from a concrete ultrastrong closed ball, regarded in Sakai's
coefficient-series sigma-WOT square ball. -/
private def usotSquareSigmaWOT (N : NonUnitalStarSubalgebra ℂ BH) (r : ℝ)
    (x a : BoundedOperatorTopology.USOTClosedBall (N : Set BH) r) :
    BoundedOperatorTopology.SigmaWOTClosedBall (N : Set BH) ((2 * r) ^ 2) := by
  let D : BH := a.1.toCLM - x.1.toCLM
  have hD : D ∈ N := N.sub_mem a.2.1 x.2.1
  exact ⟨ContinuousLinearMap.vectorFunctionalSeriesWeakOfCLM (star D * D),
    N.mul_mem (StarMemClass.star_mem (s := N) hD) hD,
    by
      change ‖star D * D‖ ≤ (2 * r) ^ 2
      simpa only [D, two_mul] using
        (CStarRing.norm_star_sub_mul_self_le_add_sq
          (R := BH) (a := a.1.toCLM) (x := x.1.toCLM) a.2.2 x.2.2)⟩

/-- Arbitrary-filter form of the intrinsic-strong/SOT comparison on a closed norm ball. This is
the convergence engine used to construct the corresponding homeomorphism. -/
theorem IsUltraweakClosed.tendsto_sot_iff_inducedStrong
    {N : NonUnitalStarSubalgebra ℂ BH}
    (hN : N.IsUltraweakClosed (P := BHPredual)) (r : ℝ)
    {I : Type*} {l : Filter I}
    (f : I → InducedStrongClosedBall N hN r)
    (x : InducedStrongClosedBall N hN r) :
    Tendsto ((hN.inducedStrongSOTClosedBallEquiv r) ∘ f) l
        (nhds (hN.inducedStrongSOTClosedBallEquiv r x)) ↔
      Tendsto f l (nhds x) := by
  letI : NonUnitalCStarAlgebra N := hN.nonUnitalCStarAlgebra N
  letI : IsUnital N := hN.isUnital N
  letI : CStarAlgebra N := IsUnital.toCStarAlgebra
  letI : PartialOrder N := CStarAlgebra.spectralOrder N
  letI : StarOrderedRing N := CStarAlgebra.spectralOrderedRing N
  letI : Predual ℂ N (BHPredual ⧸
      Ultraweak.preannihilator (P := BHPredual) N.toSubmodule) :=
    hN.inducedPredual N
  rw [tendsto_subtype_rng, tendsto_subtype_rng]
  have hsot := PointwiseConvergenceCLM.tendsto_iff_wot_star_mul_self
    (l := l)
    (T := fun i ↦ (hN.inducedStrongSOTClosedBallEquiv r (f i)).1)
    (A := (hN.inducedStrongSOTClosedBallEquiv r x).1)
  have hstrong := Ultraweak.Strong.tendsto_iff_tendsto_star_sub_mul_self_of_eventually_norm_le
    (P := BHPredual ⧸ Ultraweak.preannihilator (P := BHPredual) N.toSubmodule)
    (l := l) (f := fun i ↦ (f i).1) (x := x.1)
    (R := (2 * r) ^ 2) (Eventually.of_forall fun i ↦
      (by
        change ‖star ((show N from (f i).1) - (show N from x.1)) *
          ((show N from (f i).1) - (show N from x.1))‖ ≤ (2 * r) ^ 2
        simpa only [two_mul] using
          (CStarRing.norm_star_sub_mul_self_le_add_sq
            (R := N) (a := (show N from (f i).1)) (x := (show N from x.1))
            (f i).2 x.2)))
  let q := fun i ↦ hN.inducedStrongSquare r x (f i)
  let qx := hN.inducedStrongSquare r x x
  let e := hN.inducedUltraweakWOTClosedBallHomeomorph ((2 * r) ^ 2)
  have hweak := hN.tendsto_wot_iff_inducedUltraweak (l := l) ((2 * r) ^ 2) q qx
  rw [tendsto_subtype_rng, tendsto_subtype_rng] at hweak
  have hwot_fun : (fun i ↦ ((e ∘ q) i).1) =
      (fun i ↦ ContinuousLinearMapWOT.ofCLM
        (star ((((show N from (f i).1) : BH) - ((show N from x.1) : BH))) *
          ((((show N from (f i).1) : BH) - ((show N from x.1) : BH))))) := by
    funext i
    apply ContinuousLinearMapWOT.toCLM_injective
    rfl
  have hwot_zero : (e qx).1 = 0 := by
    apply ContinuousLinearMapWOT.toCLM_injective
    change star (((show N from x.1) : BH) - ((show N from x.1) : BH)) *
      (((show N from x.1) : BH) - ((show N from x.1) : BH)) = 0
    simp
  have huw_fun : (fun i ↦ (q i).1) =
      (fun i ↦ toUltraweak ℂ
        (BHPredual ⧸ Ultraweak.preannihilator (P := BHPredual) N.toSubmodule)
        (star ((show N from (f i).1) - (show N from x.1)) *
          ((show N from (f i).1) - (show N from x.1)))) := by
    funext i
    rfl
  have huw_zero : qx.1 = 0 := by
    apply (Ultraweak.linearEquiv ℂ N
      (BHPredual ⧸ Ultraweak.preannihilator (P := BHPredual) N.toSubmodule)).injective
    change star ((show N from x.1) - (show N from x.1)) *
      ((show N from x.1) - (show N from x.1)) = 0
    simp
  rw [hwot_fun, hwot_zero, huw_fun, huw_zero] at hweak
  change
    Tendsto
        (fun i ↦ (hN.inducedStrongSOTClosedBallEquiv r (f i)).1)
        l (nhds (hN.inducedStrongSOTClosedBallEquiv r x).1) ↔
      Tendsto (fun i ↦ (f i).1) l (nhds x.1)
  exact hsot.trans (hweak.trans hstrong.symm)

/-- Sakai, Proposition 1.15.2(2): on every closed norm ball in an ultraweakly closed concrete
self-adjoint operator algebra, the intrinsic strong topology agrees with SOT. In this setting
ultraweak closedness is equivalent to Sakai's WOT-closedness hypothesis. -/
def IsUltraweakClosed.inducedStrongSOTClosedBallHomeomorph
    {N : NonUnitalStarSubalgebra ℂ BH}
    (hN : N.IsUltraweakClosed (P := BHPredual)) (r : ℝ) :
    InducedStrongClosedBall N hN r ≃ₜ
      BoundedOperatorTopology.SOTClosedBall (N : Set BH) r where
  toEquiv := hN.inducedStrongSOTClosedBallEquiv r
  continuous_toFun := by
    rw [continuous_iff_continuousAt]
    intro x
    change Tendsto (fun y ↦ hN.inducedStrongSOTClosedBallEquiv r y)
      (nhds x) (nhds (hN.inducedStrongSOTClosedBallEquiv r x))
    convert (hN.tendsto_sot_iff_inducedStrong r id x).mpr tendsto_id using 1
    funext y
    rfl
  continuous_invFun := by
    rw [continuous_iff_continuousAt]
    intro x
    apply (hN.tendsto_sot_iff_inducedStrong r
      (fun y ↦ (hN.inducedStrongSOTClosedBallEquiv r).symm y)
      ((hN.inducedStrongSOTClosedBallEquiv r).symm x)).mp
    convert (tendsto_id : Tendsto id (nhds x) (nhds x)) using 1
    · funext y
      exact (hN.inducedStrongSOTClosedBallEquiv r).apply_symm_apply y
    · rw [(hN.inducedStrongSOTClosedBallEquiv r).apply_symm_apply]

@[simp]
lemma IsUltraweakClosed.inducedStrongSOTClosedBallHomeomorph_apply
    {N : NonUnitalStarSubalgebra ℂ BH}
    (hN : N.IsUltraweakClosed (P := BHPredual)) (r : ℝ)
    (T : InducedStrongClosedBall N hN r) :
    (show BH from (hN.inducedStrongSOTClosedBallHomeomorph r T).1) =
      ((show N from T.1) : BH) :=
  rfl

@[simp]
lemma IsUltraweakClosed.inducedStrongSOTClosedBallHomeomorph_symm_apply
    {N : NonUnitalStarSubalgebra ℂ BH}
    (hN : N.IsUltraweakClosed (P := BHPredual)) (r : ℝ)
    (T : BoundedOperatorTopology.SOTClosedBall (N : Set BH) r) :
    ((show N from ((hN.inducedStrongSOTClosedBallHomeomorph r).symm T).1) : BH) =
      (show BH from T.1) :=
  rfl

/-- Arbitrary-filter form of the concrete ultrastrong/SOT comparison on a closed norm ball. -/
theorem IsUltraweakClosed.tendsto_sot_iff_usot
    {N : NonUnitalStarSubalgebra ℂ BH}
    (hN : N.IsUltraweakClosed (P := BHPredual)) (r : ℝ)
    {I : Type*} {l : Filter I}
    (f : I → BoundedOperatorTopology.USOTClosedBall (N : Set BH) r)
    (x : BoundedOperatorTopology.USOTClosedBall (N : Set BH) r) :
    Tendsto ((BoundedOperatorTopology.usotSOTClosedBallEquiv (N : Set BH) r) ∘ f) l
        (nhds (BoundedOperatorTopology.usotSOTClosedBallEquiv (N : Set BH) r x)) ↔
      Tendsto f l (nhds x) := by
  rw [tendsto_subtype_rng, tendsto_subtype_rng]
  let eUS := BoundedOperatorTopology.usotSOTClosedBallEquiv (N : Set BH) r
  have hsot := PointwiseConvergenceCLM.tendsto_iff_wot_star_mul_self
    (l := l) (T := fun i ↦ (eUS (f i)).1) (A := (eUS x).1)
  have husot := BoundedOperatorUltrastrong.tendsto_iff_vectorFunctionalSeriesWeak_positiveSquare
    (l := l) (u := fun i ↦ (f i).1) (T := x.1)
  let q := fun i ↦ N.usotSquareSigmaWOT r x (f i)
  let qx := N.usotSquareSigmaWOT r x x
  let eW := hN.sigmaWOTWOTClosedBallHomeomorph N ((2 * r) ^ 2)
  have hweak :
      Tendsto (eW ∘ q) l (nhds (eW qx)) ↔ Tendsto q l (nhds qx) :=
    eW.isInducing.tendsto_nhds_iff.symm
  rw [tendsto_subtype_rng, tendsto_subtype_rng] at hweak
  have hwot_fun : (fun i ↦ ((eW ∘ q) i).1) =
      (fun i ↦ ContinuousLinearMapWOT.ofCLM
        (star ((f i).1.toCLM - x.1.toCLM) *
          ((f i).1.toCLM - x.1.toCLM))) := by
    funext i
    apply ContinuousLinearMapWOT.toCLM_injective
    rfl
  have hwot_zero : (eW qx).1 = 0 := by
    apply ContinuousLinearMapWOT.toCLM_injective
    change star (x.1.toCLM - x.1.toCLM) * (x.1.toCLM - x.1.toCLM) = 0
    simp
  have hsigma_fun : (fun i ↦ (q i).1) =
      (fun i ↦ ContinuousLinearMap.vectorFunctionalSeriesWeakOfCLM
        (star ((f i).1.toCLM - x.1.toCLM) *
          ((f i).1.toCLM - x.1.toCLM))) := by
    funext i
    rfl
  have hsigma_zero : qx.1 =
      ContinuousLinearMap.vectorFunctionalSeriesWeakOfCLM (0 : BH) := by
    apply (WeakBilin.linearEquiv ℂ
      (Ultraweak.testPairing
        (M := BH) (ContinuousLinearMap.vectorFunctionalSeriesSpan (H := H)))).injective
    change star (x.1.toCLM - x.1.toCLM) * (x.1.toCLM - x.1.toCLM) = 0
    simp
  rw [hwot_fun, hwot_zero, hsigma_fun, hsigma_zero] at hweak
  change
    Tendsto (fun i ↦ (eUS (f i)).1) l (nhds (eUS x).1) ↔
      Tendsto (fun i ↦ (f i).1) l (nhds x.1)
  exact hsot.trans (hweak.trans husot.symm)

/-- Sakai, Proposition 1.15.2(2): on every closed norm ball in an ultraweakly closed concrete
self-adjoint operator algebra, Sakai's coefficient-series ultrastrong topology agrees with SOT.
In this setting ultraweak closedness is equivalent to Sakai's WOT-closedness hypothesis. -/
def IsUltraweakClosed.usotSOTClosedBallHomeomorph
    {N : NonUnitalStarSubalgebra ℂ BH}
    (hN : N.IsUltraweakClosed (P := BHPredual)) (r : ℝ) :
    BoundedOperatorTopology.USOTClosedBall (N : Set BH) r ≃ₜ
      BoundedOperatorTopology.SOTClosedBall (N : Set BH) r where
  toEquiv := BoundedOperatorTopology.usotSOTClosedBallEquiv (N : Set BH) r
  continuous_toFun :=
    BoundedOperatorTopology.continuous_usotSOTClosedBallEquiv (N : Set BH) r
  continuous_invFun := by
    rw [continuous_iff_continuousAt]
    intro x
    apply (hN.tendsto_sot_iff_usot r
      (fun y ↦ (BoundedOperatorTopology.usotSOTClosedBallEquiv
        (N : Set BH) r).symm y)
      ((BoundedOperatorTopology.usotSOTClosedBallEquiv
        (N : Set BH) r).symm x)).mp
    convert (tendsto_id : Tendsto id (nhds x) (nhds x)) using 1
    · funext y
      exact (BoundedOperatorTopology.usotSOTClosedBallEquiv
        (N : Set BH) r).apply_symm_apply y
    · rw [(BoundedOperatorTopology.usotSOTClosedBallEquiv
        (N : Set BH) r).apply_symm_apply]

@[simp]
lemma IsUltraweakClosed.usotSOTClosedBallHomeomorph_apply
    {N : NonUnitalStarSubalgebra ℂ BH}
    (hN : N.IsUltraweakClosed (P := BHPredual)) (r : ℝ)
    (T : BoundedOperatorTopology.USOTClosedBall (N : Set BH) r) :
    (show BH from (hN.usotSOTClosedBallHomeomorph r T).1) = T.1.toCLM :=
  rfl

@[simp]
lemma IsUltraweakClosed.usotSOTClosedBallHomeomorph_symm_apply
    {N : NonUnitalStarSubalgebra ℂ BH}
    (hN : N.IsUltraweakClosed (P := BHPredual)) (r : ℝ)
    (T : BoundedOperatorTopology.SOTClosedBall (N : Set BH) r) :
    ((hN.usotSOTClosedBallHomeomorph r).symm T).1.toCLM = (show BH from T.1) :=
  rfl

/-- Sakai, Proposition 1.15.2(2): on every closed norm ball in an ultraweakly closed concrete
self-adjoint operator algebra, the intrinsic strong and coefficient-series ultrastrong topologies
agree. In this setting ultraweak closedness is equivalent to Sakai's WOT-closedness hypothesis. -/
def IsUltraweakClosed.inducedStrongUSOTClosedBallHomeomorph
    {N : NonUnitalStarSubalgebra ℂ BH}
    (hN : N.IsUltraweakClosed (P := BHPredual)) (r : ℝ) :
    InducedStrongClosedBall N hN r ≃ₜ
      BoundedOperatorTopology.USOTClosedBall (N : Set BH) r :=
  (hN.inducedStrongSOTClosedBallHomeomorph r).trans
    (hN.usotSOTClosedBallHomeomorph r).symm

@[simp]
lemma IsUltraweakClosed.inducedStrongUSOTClosedBallHomeomorph_apply
    {N : NonUnitalStarSubalgebra ℂ BH}
    (hN : N.IsUltraweakClosed (P := BHPredual)) (r : ℝ)
    (T : InducedStrongClosedBall N hN r) :
    (hN.inducedStrongUSOTClosedBallHomeomorph r T).1.toCLM =
      ((show N from T.1) : BH) :=
  rfl

@[simp]
lemma IsUltraweakClosed.inducedStrongUSOTClosedBallHomeomorph_symm_apply
    {N : NonUnitalStarSubalgebra ℂ BH}
    (hN : N.IsUltraweakClosed (P := BHPredual)) (r : ℝ)
    (T : BoundedOperatorTopology.USOTClosedBall (N : Set BH) r) :
    ((show N from ((hN.inducedStrongUSOTClosedBallHomeomorph r).symm T).1) : BH) =
      T.1.toCLM :=
  rfl

/-- Arbitrary-filter form of the intrinsic-strong/concrete-ultrastrong closed-ball
homeomorphism in Sakai, Proposition 1.15.2(2). -/
theorem IsUltraweakClosed.tendsto_usot_iff_inducedStrong
    {N : NonUnitalStarSubalgebra ℂ BH}
    (hN : N.IsUltraweakClosed (P := BHPredual)) (r : ℝ)
    {I : Type*} {l : Filter I}
    (f : I → InducedStrongClosedBall N hN r)
    (x : InducedStrongClosedBall N hN r) :
    Tendsto ((hN.inducedStrongUSOTClosedBallHomeomorph r) ∘ f) l
        (nhds (hN.inducedStrongUSOTClosedBallHomeomorph r x)) ↔
      Tendsto f l (nhds x) :=
  (hN.inducedStrongUSOTClosedBallHomeomorph r).isInducing.tendsto_nhds_iff.symm

end BoundedOperators

end NonUnitalStarSubalgebra
