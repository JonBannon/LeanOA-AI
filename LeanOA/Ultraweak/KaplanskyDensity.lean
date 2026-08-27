module

public import LeanOA.CStarAlgebra.KaplanskyDensity
public import LeanOA.Mackey
public import LeanOA.Mathlib.Analysis.Convex.Topology
public import LeanOA.Ultraweak.Dual
public import LeanOA.Ultraweak.Multiplication
public import LeanOA.Ultraweak.Strong
public import Mathlib.Analysis.Convex.KreinMilman
public import Mathlib.Topology.Algebra.Star.LinearMap

@[expose] public section

open Filter Set
open scoped ComplexOrder Ultraweak

namespace Ultraweak

section PredualMap

variable {𝕜 M P : Type*} [RCLike 𝕜]
  [NormedAddCommGroup M] [NormedSpace 𝕜 M]
  [NormedAddCommGroup P] [NormedSpace 𝕜 P] [Predual 𝕜 M P]

/-- The transpose on a specified predual of a continuous linear endomorphism of the corresponding
ultraweak space. -/
noncomputable def continuousDualMap (T : σ(M, P)_𝕜 →L[𝕜] σ(M, P)_𝕜) :
    StrongDual 𝕜 (σ(M, P)_𝕜) →ₗ[𝕜] StrongDual 𝕜 (σ(M, P)_𝕜) where
  toFun f := f.comp T
  map_add' f g := by ext; simp
  map_smul' c f := by ext; simp

@[simp]
lemma continuousDualMap_apply (T : σ(M, P)_𝕜 →L[𝕜] σ(M, P)_𝕜)
    (f : StrongDual 𝕜 (σ(M, P)_𝕜)) : continuousDualMap T f = f.comp T := rfl

/-- The transpose on a specified predual of a continuous linear endomorphism of the corresponding
ultraweak space. -/
noncomputable def predualMap (T : σ(M, P)_𝕜 →L[𝕜] σ(M, P)_𝕜) : P →ₗ[𝕜] P :=
  (predualDualEquiv 𝕜 M P).symm.toLinearMap.comp <|
    (continuousDualMap T).comp (predualDualEquiv 𝕜 M P).toLinearMap

@[simp]
lemma predualDualEquiv_predualMap (T : σ(M, P)_𝕜 →L[𝕜] σ(M, P)_𝕜) (p : P) :
    predualDualEquiv 𝕜 M P (predualMap T p) = (predualDualEquiv 𝕜 M P p).comp T := by
  simp [predualMap]

lemma pairing_predualMap (T : σ(M, P)_𝕜 →L[𝕜] σ(M, P)_𝕜) (x : σ(M, P)_𝕜)
    (p : P) : pairing 𝕜 M P x (predualMap T p) = pairing 𝕜 M P (T x) p := by
  simp [← predualDualEquiv_apply_apply]

end PredualMap

section StarAction

variable {M P : Type*} [CStarAlgebra M]
  [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]

/-- The involution on a dual C⋆-algebra, transposed to its specified predual.  Thus
`predualStar p` represents the functional `x ↦ conj (p (star x))`.

This is conjugate-linear, rather than complex-linear; the bundled version is `predualStarL`. -/
noncomputable def predualStar (p : P) : P :=
  (predualDualEquiv ℂ M P).symm <|
    (star (WithConv.toConv (predualDualEquiv ℂ M P p))).ofConv

@[simp]
lemma predualDualEquiv_predualStar (p : P) :
    predualDualEquiv ℂ M P (predualStar (M := M) p) =
      (star (WithConv.toConv (predualDualEquiv ℂ M P p))).ofConv := by
  simp [predualStar]

lemma pairing_predualStar (x : σ(M, P)) (p : P) :
    pairing ℂ M P x (predualStar (M := M) p) =
      star (pairing ℂ M P (star x) p) := by
  change predualDualEquiv ℂ M P (predualStar (M := M) p) x =
    star (predualDualEquiv ℂ M P p (star x))
  rw [predualDualEquiv_predualStar]
  rfl

@[simp]
lemma predualStar_add (p q : P) :
    predualStar (M := M) (p + q) =
      predualStar (M := M) p + predualStar (M := M) q := by
  apply (predualDualEquiv ℂ M P).injective
  simp

@[simp]
lemma predualStar_smul (c : ℂ) (p : P) :
    predualStar (M := M) (c • p) = star c • predualStar (M := M) p := by
  apply (predualDualEquiv ℂ M P).injective
  ext x
  simp

@[simp]
lemma predualStar_predualStar (p : P) :
    predualStar (M := M) (predualStar (M := M) p) = p := by
  apply (predualDualEquiv ℂ M P).injective
  ext x
  simp

/-- The canonical conjugate-linear involution on a specified predual. -/
noncomputable def predualStarLinearEquiv : P ≃ₗ⋆[ℂ] P where
  toFun := predualStar (M := M)
  map_add' := predualStar_add (M := M)
  map_smul' := predualStar_smul (M := M)
  invFun := predualStar (M := M)
  left_inv := predualStar_predualStar (M := M)
  right_inv := predualStar_predualStar (M := M)

private lemma toDualₗᵢ_predualStar (p : P) :
    Predual.toDualₗᵢ (𝕜 := ℂ) (M := M) (P := P) (predualStar (M := M) p) =
      (star (WithConv.toConv
        (Predual.toDualₗᵢ (𝕜 := ℂ) (M := M) (P := P) p))).ofConv := by
  ext x
  exact pairing_predualStar (toUltraweak ℂ P x) p

lemma norm_predualStar_le (p : P) : ‖predualStar (M := M) p‖ ≤ ‖p‖ := by
  rw [← (Predual.toDualₗᵢ (𝕜 := ℂ) (M := M) (P := P)).norm_map,
    toDualₗᵢ_predualStar]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg p)
  intro x
  rw [ContinuousLinearMap.intrinsicStar_apply, norm_star]
  calc
    _ ≤ ‖Predual.toDualₗᵢ (𝕜 := ℂ) (M := M) (P := P) p‖ * ‖star x‖ :=
      (Predual.toDualₗᵢ (𝕜 := ℂ) (M := M) (P := P) p).le_opNorm (star x)
    _ = ‖p‖ * ‖x‖ := by
      rw [(Predual.toDualₗᵢ (𝕜 := ℂ) (M := M) (P := P)).norm_map, norm_star]

lemma norm_predualStar (p : P) : ‖predualStar (M := M) p‖ = ‖p‖ := by
  apply le_antisymm (norm_predualStar_le (M := M) p)
  simpa only [predualStar_predualStar] using
    norm_predualStar_le (M := M) (predualStar (M := M) p)

/-- The canonical isometric conjugate-linear involution on a specified predual. -/
noncomputable def predualStarLI : P ≃ₗᵢ⋆[ℂ] P where
  toLinearEquiv := predualStarLinearEquiv (M := M)
  norm_map' := norm_predualStar (M := M)

/-- The bounded canonical conjugate-linear involution on a specified predual. -/
noncomputable def predualStarL : P ≃L⋆[ℂ] P :=
  (predualStarLI (M := M)).toContinuousLinearEquiv

@[simp]
lemma predualStarL_apply (p : P) :
    predualStarL (M := M) p = predualStar (M := M) p := rfl

end StarAction

section MultiplicationActions

variable {M P : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]

/-- The left action of a C⋆-algebra on itself, transposed to its specified predual. -/
noncomputable def predualMulLeft (a : M) : P →ₗ[ℂ] P :=
  predualMap (mulLeftL (P := P) a)

/-- The right action of a C⋆-algebra on itself, transposed to its specified predual. -/
noncomputable def predualMulRight (a : M) : P →ₗ[ℂ] P :=
  predualMap (mulRightL (P := P) a)

lemma pairing_predualMulLeft (a : M) (x : σ(M, P)) (p : P) :
    pairing ℂ M P x (predualMulLeft a p) =
      pairing ℂ M P (toUltraweak ℂ P (a * ofUltraweak x)) p := by
  rw [predualMulLeft, pairing_predualMap]
  rfl

lemma pairing_predualMulRight (a : M) (x : σ(M, P)) (p : P) :
    pairing ℂ M P x (predualMulRight a p) =
      pairing ℂ M P (toUltraweak ℂ P (ofUltraweak x * a)) p := by
  rw [predualMulRight, pairing_predualMap]
  rfl

private lemma toDualₗᵢ_predualMulLeft (a : M) (p : P) :
    Predual.toDualₗᵢ (𝕜 := ℂ) (M := M) (P := P) (predualMulLeft a p) =
      (Predual.toDualₗᵢ (𝕜 := ℂ) (M := M) (P := P) p).comp
        (ContinuousLinearMap.mul ℂ M a) := by
  ext x
  exact pairing_predualMulLeft a (toUltraweak ℂ P x) p

private lemma toDualₗᵢ_predualMulRight (a : M) (p : P) :
    Predual.toDualₗᵢ (𝕜 := ℂ) (M := M) (P := P) (predualMulRight a p) =
      (Predual.toDualₗᵢ (𝕜 := ℂ) (M := M) (P := P) p).comp
        ((ContinuousLinearMap.mul ℂ M).flip a) := by
  ext x
  exact pairing_predualMulRight a (toUltraweak ℂ P x) p

lemma norm_predualMulLeft_le (a : M) (p : P) : ‖predualMulLeft a p‖ ≤ ‖a‖ * ‖p‖ := by
  rw [← (Predual.toDualₗᵢ (𝕜 := ℂ) (M := M) (P := P)).norm_map,
    toDualₗᵢ_predualMulLeft]
  calc
    _ ≤ ‖Predual.toDualₗᵢ (𝕜 := ℂ) (M := M) (P := P) p‖ *
        ‖ContinuousLinearMap.mul ℂ M a‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖p‖ * ‖a‖ := mul_le_mul
      ((Predual.toDualₗᵢ (𝕜 := ℂ) (M := M) (P := P)).norm_map p).le
      (ContinuousLinearMap.opNorm_mul_apply_le ℂ M a) (norm_nonneg _) (norm_nonneg _)
    _ = ‖a‖ * ‖p‖ := mul_comm _ _

lemma norm_predualMulRight_le (a : M) (p : P) : ‖predualMulRight a p‖ ≤ ‖a‖ * ‖p‖ := by
  rw [← (Predual.toDualₗᵢ (𝕜 := ℂ) (M := M) (P := P)).norm_map,
    toDualₗᵢ_predualMulRight]
  calc
    _ ≤ ‖Predual.toDualₗᵢ (𝕜 := ℂ) (M := M) (P := P) p‖ *
        ‖(ContinuousLinearMap.mul ℂ M).flip a‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖p‖ * ‖a‖ := by
      gcongr
      · exact (Predual.toDualₗᵢ (𝕜 := ℂ) (M := M) (P := P)).norm_map p |>.le
      · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a)
        intro x
        change ‖x * a‖ ≤ ‖a‖ * ‖x‖
        simpa only [mul_comm ‖a‖ ‖x‖] using norm_mul_le x a
    _ = ‖a‖ * ‖p‖ := mul_comm _ _

/-- The bounded left action on the specified predual. -/
noncomputable def predualMulLeftL (a : M) : P →L[ℂ] P :=
  LinearMap.mkContinuous (predualMulLeft a) ‖a‖ (norm_predualMulLeft_le a)

/-- The bounded right action on the specified predual. -/
noncomputable def predualMulRightL (a : M) : P →L[ℂ] P :=
  LinearMap.mkContinuous (predualMulRight a) ‖a‖ (norm_predualMulRight_le a)

@[simp]
lemma predualMulLeftL_apply (a : M) (p : P) : predualMulLeftL a p = predualMulLeft a p := rfl

@[simp]
lemma predualMulRightL_apply (a : M) (p : P) : predualMulRightL a p = predualMulRight a p := rfl

end MultiplicationActions

section InvariantTestSpace

variable {M P : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]

/-- A norm-dense subspace of a specified predual which is stable under the canonical predual
involution and under the transposes of all fixed left and right multiplications.

This is deliberately a predicate on a chosen submodule, rather than a typeclass: the same
specified predual can contain several useful invariant test spaces. -/
structure SakaiInvariantTestSpace (V : Submodule ℂ P) : Prop where
  /-- The test space is norm-dense in the specified predual. -/
  dense : Dense (V : Set P)
  /-- The test space is stable under the predual involution. -/
  predualStar_mem : ∀ p : V, predualStar (M := M) (P := P) p.1 ∈ V
  /-- The test space is stable under the transpose of fixed left multiplication. -/
  predualMulLeft_mem : ∀ (a : M) (p : V), predualMulLeft (P := P) a p.1 ∈ V
  /-- The test space is stable under the transpose of fixed right multiplication. -/
  predualMulRight_mem : ∀ (a : M) (p : V), predualMulRight (P := P) a p.1 ∈ V

namespace SakaiInvariantTestSpace

/-- The whole specified predual is a Sakai-invariant test space. -/
protected theorem top : SakaiInvariantTestSpace (M := M) (⊤ : Submodule ℂ P) where
  dense := by simp
  predualStar_mem := fun _ ↦ trivial
  predualMulLeft_mem := fun _ _ ↦ trivial
  predualMulRight_mem := fun _ _ ↦ trivial

/-- The canonical predual involution restricted to an invariant test space. -/
noncomputable def predualStarL {V : Submodule ℂ P} (hV : SakaiInvariantTestSpace (M := M) V) :
    V ≃L⋆[ℂ] V where
  toFun p := ⟨predualStar (M := M) (P := P) p.1, hV.predualStar_mem p⟩
  invFun p := ⟨predualStar (M := M) (P := P) p.1, hV.predualStar_mem p⟩
  left_inv p := Subtype.ext <| predualStar_predualStar (M := M) (P := P) p.1
  right_inv p := Subtype.ext <| predualStar_predualStar (M := M) (P := P) p.1
  map_add' p q := Subtype.ext <| predualStar_add (M := M) (P := P) p.1 q.1
  map_smul' c p := Subtype.ext <| predualStar_smul (M := M) (P := P) c p.1
  continuous_toFun := by
    exact (Ultraweak.predualStarL (M := M) (P := P)).continuous.comp
      continuous_subtype_val |>.subtype_mk _
  continuous_invFun := by
    exact (Ultraweak.predualStarL (M := M) (P := P)).continuous.comp
      continuous_subtype_val |>.subtype_mk _

@[simp]
lemma predualStarL_apply {V : Submodule ℂ P} (hV : SakaiInvariantTestSpace (M := M) V)
    (p : V) : (hV.predualStarL p : P) = predualStar (M := M) (P := P) p.1 := rfl

/-- The transpose of fixed left multiplication, restricted to an invariant test space. -/
noncomputable def predualMulLeftL {V : Submodule ℂ P}
    (hV : SakaiInvariantTestSpace (M := M) V) (a : M) : V →L[ℂ] V :=
  (Ultraweak.predualMulLeftL (P := P) a).restrict fun p hp ↦
    hV.predualMulLeft_mem a ⟨p, hp⟩

/-- The transpose of fixed right multiplication, restricted to an invariant test space. -/
noncomputable def predualMulRightL {V : Submodule ℂ P}
    (hV : SakaiInvariantTestSpace (M := M) V) (a : M) : V →L[ℂ] V :=
  (Ultraweak.predualMulRightL (P := P) a).restrict fun p hp ↦
    hV.predualMulRight_mem a ⟨p, hp⟩

@[simp]
lemma predualMulLeftL_apply {V : Submodule ℂ P}
    (hV : SakaiInvariantTestSpace (M := M) V) (a : M) (p : V) :
    (hV.predualMulLeftL a p : P) = predualMulLeft (P := P) a p.1 := rfl

@[simp]
lemma predualMulRightL_apply {V : Submodule ℂ P}
    (hV : SakaiInvariantTestSpace (M := M) V) (a : M) (p : V) :
    (hV.predualMulRightL a p : P) = predualMulRight (P := P) a p.1 := rfl

end SakaiInvariantTestSpace

end InvariantTestSpace

section RestrictedPairing

variable {M P : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]

/-- The norm-bounded evaluation pairing of a dual space with its specified predual. -/
noncomputable def normPairing : M →L[ℂ] P →L[ℂ] ℂ :=
  Predual.equivDual.toContinuousLinearEquiv.toContinuousLinearMap

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace P] in
@[simp]
lemma normPairing_apply (x : M) (p : P) :
    normPairing (M := M) (P := P) x p = Predual.equivDual x p := rfl

/-- Evaluation restricted to a chosen submodule of the specified predual. -/
noncomputable def testPairing (V : Submodule ℂ P) : M →ₗ[ℂ] V →ₗ[ℂ] ℂ :=
  (((ContinuousLinearMap.coeLM ℂ).comp
    (normPairing (M := M) (P := P)).toLinearMap).flip.comp V.subtype).flip

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace P] in
@[simp]
lemma testPairing_apply (V : Submodule ℂ P) (x : M) (p : V) :
    testPairing (M := M) V x p = Predual.equivDual x p.1 := rfl

/-- The chosen test space with the weak topology induced by evaluation against `M`. -/
abbrev WeakTestSpace (V : Submodule ℂ P) := WeakBilin (testPairing (M := M) V).flip

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace P] in
private lemma testPairing_flip_injective (V : Submodule ℂ P) :
    Function.Injective (testPairing (M := M) V).flip := by
  intro p q hpq
  apply Subtype.ext
  apply (Predual.toDualₗᵢ (𝕜 := ℂ) (M := M) (P := P)).injective
  ext x
  simpa [LinearMap.flip_apply] using DFunLike.congr_fun hpq x

noncomputable instance weakTestSpaceT1 (V : Submodule ℂ P) :
    T1Space (WeakTestSpace (M := M) V) :=
  (WeakBilin.isEmbedding (testPairing_flip_injective (M := M) V)).t1Space

/-- The pairing used to put the Mackey topology `τ(M,V)` on `M`.  Its right coordinate is
definitionally `V`, but carries the weak topology induced by evaluation against `M`. -/
noncomputable def mackeyTestPairing (V : Submodule ℂ P) :
    M →ₗ[ℂ] WeakTestSpace (M := M) V →ₗ[ℂ] ℂ :=
  (WeakBilin.pairing (testPairing (M := M) V).flip).flip

noncomputable instance mackeyTestPairing_flip_isWeak (V : Submodule ℂ P) :
    (mackeyTestPairing (M := M) V).flip.IsWeak := by
  unfold mackeyTestPairing
  infer_instance

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace P] in
@[simp]
lemma mackeyTestPairing_apply (V : Submodule ℂ P) (x : M)
    (p : WeakTestSpace (M := M) V) :
    mackeyTestPairing (M := M) V x p = Predual.equivDual x p.1 := rfl

/-- Sakai's Mackey topology `τ(M,V)` associated to a chosen predual test space. -/
abbrev SakaiMackey (V : Submodule ℂ P) := Mackey (mackeyTestPairing (M := M) V)

private lemma testPairing_injective {V : Submodule ℂ P}
    (hV : SakaiInvariantTestSpace (M := M) V) :
    Function.Injective (testPairing (M := M) V) := by
  intro x y hxy
  apply (Predual.equivDual (𝕜 := ℂ) (M := M) (P := P)).injective
  apply ContinuousLinearMap.ext
  have hfun := Continuous.ext_on hV.dense
    (Predual.equivDual (M := M) (P := P) x).continuous
    (Predual.equivDual (M := M) (P := P) y).continuous
    (fun p hp ↦ DFunLike.congr_fun hxy ⟨p, hp⟩)
  exact fun p ↦ congrFun hfun p

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace P] in
private lemma absConvex_ultraweak_unitClosedBall :
    AbsConvex ℂ (ofUltraweak ⁻¹' Metric.closedBall (0 : M) 1 : Set σ(M, P)) := by
  have hball : AbsConvex ℂ (Metric.closedBall (0 : M) 1) :=
    ⟨balanced_closedBall_zero,
      convex_RCLike_iff_convex_real.mpr (convex_closedBall (0 : M) 1)⟩
  let e := (Ultraweak.linearEquiv ℂ M P).toLinearMap
  exact ⟨hball.1.mulActionHom_preimage e.toMulActionHom, hball.2.linear_preimage e⟩

namespace SakaiInvariantTestSpace

/-- For a fixed test functional, the weak orbit under the transposed left action, with the
multiplier varying ultraweakly. -/
noncomputable def weakPredualMulLeftOrbitL {V : Submodule ℂ P}
    (hV : SakaiInvariantTestSpace (M := M) V) (p : V) :
    σ(M, P) →L[ℂ] WeakTestSpace (M := M) V where
  toFun a := ⟨predualMulLeft (P := P) (ofUltraweak a) p.1,
    hV.predualMulLeft_mem (ofUltraweak a) p⟩
  map_add' a b := by
    apply Subtype.ext
    apply (predualDualEquiv ℂ M P).injective
    ext x
    change pairing ℂ M P x (predualMulLeft (P := P) (ofUltraweak (a + b)) p.1) =
      pairing ℂ M P x
        (predualMulLeft (P := P) (ofUltraweak a) p.1 +
          predualMulLeft (P := P) (ofUltraweak b) p.1)
    rw [pairing_predualMulLeft, map_add,
      pairing_predualMulLeft, pairing_predualMulLeft]
    rw [ofUltraweak_add, add_mul, toUltraweak_add]
    exact map_add ((pairing ℂ M P).flip p.1) _ _
  map_smul' c a := by
    apply Subtype.ext
    apply (predualDualEquiv ℂ M P).injective
    ext x
    change pairing ℂ M P x (predualMulLeft (P := P) (ofUltraweak (c • a)) p.1) =
      pairing ℂ M P x (c • predualMulLeft (P := P) (ofUltraweak a) p.1)
    rw [pairing_predualMulLeft, map_smul,
      pairing_predualMulLeft]
    change pairing ℂ M P
      (toUltraweak ℂ P ((c • ofUltraweak a) * ofUltraweak x)) p.1 = _
    rw [smul_mul_assoc, toUltraweak_smul]
    exact map_smul ((pairing ℂ M P).flip p.1) c _
  cont := by
    apply WeakBilin.continuous_of_continuous_eval
    intro x
    convert (Ultraweak.eval_continuous (M := M) (P := P) p.1).comp
      (Ultraweak.mulRightL (P := P) x).continuous using 1
    funext a
    exact pairing_predualMulLeft (ofUltraweak a) (toUltraweak ℂ P x) p.1

/-- For a fixed test functional, the weak orbit under the transposed right action, with the
multiplier varying ultraweakly. -/
noncomputable def weakPredualMulRightOrbitL {V : Submodule ℂ P}
    (hV : SakaiInvariantTestSpace (M := M) V) (p : V) :
    σ(M, P) →L[ℂ] WeakTestSpace (M := M) V where
  toFun a := ⟨predualMulRight (P := P) (ofUltraweak a) p.1,
    hV.predualMulRight_mem (ofUltraweak a) p⟩
  map_add' a b := by
    apply Subtype.ext
    apply (predualDualEquiv ℂ M P).injective
    ext x
    change pairing ℂ M P x (predualMulRight (P := P) (ofUltraweak (a + b)) p.1) =
      pairing ℂ M P x
        (predualMulRight (P := P) (ofUltraweak a) p.1 +
          predualMulRight (P := P) (ofUltraweak b) p.1)
    rw [pairing_predualMulRight, map_add,
      pairing_predualMulRight, pairing_predualMulRight]
    rw [ofUltraweak_add, mul_add, toUltraweak_add]
    exact map_add ((pairing ℂ M P).flip p.1) _ _
  map_smul' c a := by
    apply Subtype.ext
    apply (predualDualEquiv ℂ M P).injective
    ext x
    change pairing ℂ M P x (predualMulRight (P := P) (ofUltraweak (c • a)) p.1) =
      pairing ℂ M P x (c • predualMulRight (P := P) (ofUltraweak a) p.1)
    rw [pairing_predualMulRight, map_smul,
      pairing_predualMulRight]
    change pairing ℂ M P
      (toUltraweak ℂ P (ofUltraweak x * (c • ofUltraweak a))) p.1 = _
    rw [mul_smul_comm, toUltraweak_smul]
    exact map_smul ((pairing ℂ M P).flip p.1) c _
  cont := by
    apply WeakBilin.continuous_of_continuous_eval
    intro x
    convert (Ultraweak.eval_continuous (M := M) (P := P) p.1).comp
      (Ultraweak.mulLeftL (P := P) x).continuous using 1
    funext a
    exact pairing_predualMulRight (ofUltraweak a) (toUltraweak ℂ P x) p.1

@[simp]
lemma weakPredualMulLeftOrbitL_apply {V : Submodule ℂ P}
    (hV : SakaiInvariantTestSpace (M := M) V) (p : V) (a : σ(M, P)) :
    (hV.weakPredualMulLeftOrbitL p a : V) =
      ⟨predualMulLeft (P := P) (ofUltraweak a) p.1,
        hV.predualMulLeft_mem (ofUltraweak a) p⟩ := rfl

@[simp]
lemma weakPredualMulRightOrbitL_apply {V : Submodule ℂ P}
    (hV : SakaiInvariantTestSpace (M := M) V) (p : V) (a : σ(M, P)) :
    (hV.weakPredualMulRightOrbitL p a : V) =
      ⟨predualMulRight (P := P) (ofUltraweak a) p.1,
        hV.predualMulRight_mem (ofUltraweak a) p⟩ := rfl

lemma mackeyTestPairing_weakPredualMulRightOrbitL {V : Submodule ℂ P}
    (hV : SakaiInvariantTestSpace (M := M) V) (p : V) (x : M) (a : σ(M, P)) :
    mackeyTestPairing (M := M) V x (hV.weakPredualMulRightOrbitL p a) =
      Predual.equivDual (x * ofUltraweak a) p.1 := by
  change Predual.equivDual x (predualMulRight (P := P) (ofUltraweak a) p.1) = _
  exact pairing_predualMulRight (ofUltraweak a) (toUltraweak ℂ P x) p.1

/-- The weakly topologized restriction of the transposed left action. -/
noncomputable def weakPredualMulLeft {V : Submodule ℂ P}
    (hV : SakaiInvariantTestSpace (M := M) V) (a : M) :
    WeakTestSpace (M := M) V →ₗ[ℂ] WeakTestSpace (M := M) V :=
  (WeakBilin.linearEquiv ℂ (testPairing (M := M) V).flip).symm.toLinearMap.comp <|
    (hV.predualMulLeftL a).toLinearMap.comp
      (WeakBilin.linearEquiv ℂ (testPairing (M := M) V).flip).toLinearMap

/-- The weakly topologized restriction of the transposed right action. -/
noncomputable def weakPredualMulRight {V : Submodule ℂ P}
    (hV : SakaiInvariantTestSpace (M := M) V) (a : M) :
    WeakTestSpace (M := M) V →ₗ[ℂ] WeakTestSpace (M := M) V :=
  (WeakBilin.linearEquiv ℂ (testPairing (M := M) V).flip).symm.toLinearMap.comp <|
    (hV.predualMulRightL a).toLinearMap.comp
      (WeakBilin.linearEquiv ℂ (testPairing (M := M) V).flip).toLinearMap

/-- The weakly topologized restriction of the canonical predual involution. -/
noncomputable def weakPredualStar {V : Submodule ℂ P}
    (hV : SakaiInvariantTestSpace (M := M) V) :
    WeakTestSpace (M := M) V →ₗ⋆[ℂ] WeakTestSpace (M := M) V where
  toFun p := (WeakBilin.linearEquiv ℂ (testPairing (M := M) V).flip).symm
    (hV.predualStarL ((WeakBilin.linearEquiv ℂ
      (testPairing (M := M) V).flip) p))
  map_add' p q := by
    change hV.predualStarL (p + q) = hV.predualStarL p + hV.predualStarL q
    exact map_add hV.predualStarL p q
  map_smul' c p := by
    change hV.predualStarL (c • p) = star c • hV.predualStarL p
    exact map_smulₛₗ hV.predualStarL c p

@[simp]
lemma weakPredualMulLeft_apply {V : Submodule ℂ P}
    (hV : SakaiInvariantTestSpace (M := M) V) (a : M)
    (p : WeakTestSpace (M := M) V) :
    (hV.weakPredualMulLeft a p : V) = hV.predualMulLeftL a p := rfl

@[simp]
lemma weakPredualMulRight_apply {V : Submodule ℂ P}
    (hV : SakaiInvariantTestSpace (M := M) V) (a : M)
    (p : WeakTestSpace (M := M) V) :
    (hV.weakPredualMulRight a p : V) = hV.predualMulRightL a p := rfl

@[simp]
lemma weakPredualStar_apply {V : Submodule ℂ P}
    (hV : SakaiInvariantTestSpace (M := M) V) (p : WeakTestSpace (M := M) V) :
    (hV.weakPredualStar p : V) = hV.predualStarL p := rfl

/-- Fixed left multiplication is continuous for Sakai's Mackey topology `τ(M,V)`. -/
noncomputable def mackeyMulLeftL {V : Submodule ℂ P}
    (hV : SakaiInvariantTestSpace (M := M) V) (a : M) :
    SakaiMackey (M := M) V →L[ℂ] SakaiMackey (M := M) V :=
  Mackey.map (B := mackeyTestPairing (M := M) V)
    (B' := mackeyTestPairing (M := M) V)
    (LinearMap.mulLeft ℂ a) (hV.weakPredualMulLeft a) fun x p ↦ by
    change Predual.equivDual (a * x) p.1 =
      Predual.equivDual x (predualMulLeft (P := P) a p.1)
    symm
    exact pairing_predualMulLeft a (toUltraweak ℂ P x) p.1

/-- Fixed right multiplication is continuous for Sakai's Mackey topology `τ(M,V)`. -/
noncomputable def mackeyMulRightL {V : Submodule ℂ P}
    (hV : SakaiInvariantTestSpace (M := M) V) (a : M) :
    SakaiMackey (M := M) V →L[ℂ] SakaiMackey (M := M) V :=
  Mackey.map (B := mackeyTestPairing (M := M) V)
    (B' := mackeyTestPairing (M := M) V)
    (LinearMap.mulRight ℂ a) (hV.weakPredualMulRight a) fun x p ↦ by
    change Predual.equivDual (x * a) p.1 =
      Predual.equivDual x (predualMulRight (P := P) a p.1)
    symm
    exact pairing_predualMulRight a (toUltraweak ℂ P x) p.1

/-- Involution is continuous for Sakai's Mackey topology `τ(M,V)`. -/
noncomputable def mackeyStarL {V : Submodule ℂ P}
    (hV : SakaiInvariantTestSpace (M := M) V) :
    SakaiMackey (M := M) V →L⋆[ℂ] SakaiMackey (M := M) V :=
  Mackey.mapStar (B := mackeyTestPairing (M := M) V)
    (B' := mackeyTestPairing (M := M) V)
    (starLinearEquiv ℂ (A := M)).toLinearMap hV.weakPredualStar fun x p ↦ by
    change Predual.equivDual (star x) p.1 =
      star (Predual.equivDual x (predualStar (M := M) (P := P) p.1))
    have h : Predual.equivDual x (predualStar (M := M) (P := P) p.1) =
        star (Predual.equivDual (star x) p.1) :=
      pairing_predualStar (toUltraweak ℂ P x) p.1
    simpa only [star_star] using (congrArg star h).symm

@[simp]
lemma mackeyMulLeftL_apply {V : Submodule ℂ P}
    (hV : SakaiInvariantTestSpace (M := M) V) (a : M)
    (x : SakaiMackey (M := M) V) :
    hV.mackeyMulLeftL a x = toMackey _ (a * ofMackey x) := by
  simp [mackeyMulLeftL]

@[simp]
lemma mackeyMulRightL_apply {V : Submodule ℂ P}
    (hV : SakaiInvariantTestSpace (M := M) V) (a : M)
    (x : SakaiMackey (M := M) V) :
    hV.mackeyMulRightL a x = toMackey _ (ofMackey x * a) := by
  simp [mackeyMulRightL]

@[simp]
lemma mackeyStarL_apply {V : Submodule ℂ P}
    (hV : SakaiInvariantTestSpace (M := M) V) (x : SakaiMackey (M := M) V) :
    hV.mackeyStarL x = toMackey _ (star (ofMackey x)) := by
  simp [mackeyStarL]

/-- Sakai's resolvent calculation: the Kaplansky transforms of a Mackey-convergent net converge
for the weak topology induced by the invariant test space.

The proof uses three applications of uniform convergence on the compact absolutely convex orbit
of the ultraweak unit ball.  In particular, it does not assume that the approximating net is norm
bounded. -/
theorem tendsto_kaplanskyTransform {V : Submodule ℂ P}
    (hV : SakaiInvariantTestSpace (M := M) V) {X : Type*} {l : Filter X}
    {u : X → SakaiMackey (M := M) V} {x : SakaiMackey (M := M) V}
    (hu : Tendsto u l (nhds x)) :
    Tendsto
      (fun i ↦ show WeakBilin (testPairing (M := M) V) from
        CStarAlgebra.kaplanskyTransform (A := M) (ofMackey (u i))) l
      (nhds (show WeakBilin (testPairing (M := M) V) from
        CStarAlgebra.kaplanskyTransform (A := M) (ofMackey x))) := by
  apply (WeakBilin.tendsto_iff_forall_eval_tendsto
    (B := testPairing (M := M) V)
    (testPairing_injective (M := M) hV)).2
  intro p
  let a : M := ofMackey x
  let aX : X → M := fun i ↦ ofMackey (u i)
  let r : M := CStarAlgebra.kaplanskyResolvent (A := M) a
  let rX : X → M := fun i ↦ CStarAlgebra.kaplanskyResolvent (A := M) (aX i)
  let bX : X → M := fun i ↦ aX i * rX i
  let U : Set σ(M, P) := ofUltraweak ⁻¹' Metric.closedBall (0 : M) 1
  let orbit := hV.weakPredualMulRightOrbitL p
  let K : Set (WeakTestSpace (M := M) V) := orbit '' U
  have hKc : IsCompact K := by
    exact (Ultraweak.isCompact_closedBall ℂ P (0 : M) 1).image orbit.continuous
  have hKa : AbsConvex ℂ K := by
    exact absConvex_ultraweak_unitClosedBall (M := M) (P := P) |>.image orbit.toLinearMap
  have hr_mem (i : X) : orbit (toUltraweak ℂ P (rX i)) ∈ K := by
    refine ⟨toUltraweak ℂ P (rX i), ?_, rfl⟩
    change rX i ∈ Metric.closedBall (0 : M) 1
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      CStarAlgebra.norm_kaplanskyResolvent_le_one (aX i)
  have hb_mem (i : X) : orbit (toUltraweak ℂ P (bX i)) ∈ K := by
    refine ⟨toUltraweak ℂ P (bX i), ?_, rfl⟩
    change bX i ∈ Metric.closedBall (0 : M) 1
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (CStarAlgebra.norm_mul_kaplanskyResolvent_le_half (aX i)).trans (by norm_num)
  have hd : Tendsto (fun i ↦ u i - x) l (nhds 0) := by
    convert hu.sub tendsto_const_nhds using 1
    all_goals simp
  have hstar : Tendsto (fun i ↦ hV.mackeyStarL (u i - x)) l (nhds 0) := by
    have h := (hV.mackeyStarL.continuous.tendsto 0).comp hd
    rw [map_zero] at h
    exact h.congr'
      (.of_forall fun _ ↦ rfl)
  have h₁ : Tendsto
      (fun i ↦ hV.mackeyMulLeftL (a * r) (hV.mackeyStarL (u i - x))) l (nhds 0) := by
    have h := ((hV.mackeyMulLeftL (a * r)).continuous.tendsto 0).comp hstar
    rw [map_zero] at h
    exact h.congr'
      (.of_forall fun _ ↦ rfl)
  have h₂ : Tendsto
      (fun i ↦ hV.mackeyMulLeftL (a * r * star a) (u i - x)) l (nhds 0) := by
    have h := ((hV.mackeyMulLeftL (a * r * star a)).continuous.tendsto 0).comp hd
    rw [map_zero] at h
    exact h.congr'
      (.of_forall fun _ ↦ rfl)
  have h₃ : Tendsto (fun i ↦ -(u i - x)) l (nhds 0) := by
    simpa using hd.neg
  have ht₁ := Mackey.tendsto_pairing_zero_of_tendsto_zero
    (B := mackeyTestPairing (M := M) V) h₁ hKc hKa
      (.of_forall fun i ↦ hb_mem i)
  have ht₂ := Mackey.tendsto_pairing_zero_of_tendsto_zero
    (B := mackeyTestPairing (M := M) V) h₂ hKc hKa
      (.of_forall fun i ↦ hr_mem i)
  have ht₃ := Mackey.tendsto_pairing_zero_of_tendsto_zero
    (B := mackeyTestPairing (M := M) V) h₃ hKc hKa
      (.of_forall fun i ↦ hr_mem i)
  have ht : Tendsto (fun i ↦
      mackeyTestPairing (M := M) V
          (ofMackey (hV.mackeyMulLeftL (a * r) (hV.mackeyStarL (u i - x))))
          (orbit (toUltraweak ℂ P (bX i))) +
        mackeyTestPairing (M := M) V
          (ofMackey (hV.mackeyMulLeftL (a * r * star a) (u i - x)))
          (orbit (toUltraweak ℂ P (rX i))) +
        mackeyTestPairing (M := M) V (ofMackey (-(u i - x)))
          (orbit (toUltraweak ℂ P (rX i)))) l (nhds 0) := by
    simpa only [zero_add] using (ht₁.add ht₂).add ht₃
  have ht' : Tendsto (fun i ↦
      Predual.equivDual (𝕜 := ℂ) (M := M) (P := P)
        (a * r - aX i * rX i) p.1) l (nhds 0) := by
    convert ht using 1
    funext i
    simp only [orbit, mackeyTestPairing_weakPredualMulRightOrbitL]
    simp only [mackeyMulLeftL_apply, mackeyStarL_apply, ofMackey_toMackey,
      map_sub, map_neg, ofUltraweak_toUltraweak]
    rw [← map_sub]
    rw [← add_apply, ← add_apply, ← map_add, ← map_add]
    have hra : r * (1 + star a * a) = 1 :=
      CStarAlgebra.kaplanskyResolvent_mul_one_add_star_mul_self a
    have hri : (1 + star (aX i) * aX i) * rX i = 1 :=
      CStarAlgebra.one_add_star_mul_self_mul_kaplanskyResolvent (aX i)
    have hra' : r + r * star a * a = 1 := by
      simpa only [mul_add, mul_one, mul_assoc] using hra
    have hri' : rX i + star (aX i) * aX i * rX i = 1 := by
      simpa only [add_mul, one_mul, mul_assoc] using hri
    have hra'' : 1 - r * star a * a = r := by
      rw [← hra']
      noncomm_ring
    have hri'' : star (aX i) * aX i * rX i + rX i = 1 := by
      simpa only [add_comm] using hri'
    congr 1
    congr 1
    change a * r - aX i * rX i =
      (((a * r * star (aX i) - a * r * star a) * bX i) +
        ((a * r * star a * aX i - a * r * star a * a) * rX i)) +
          (-(aX i - a) * rX i)
    dsimp only [bX]
    have hhead :
        a * (r * (star (aX i) * (aX i * rX i))) + a * (r * rX i) = a * r := by
      calc
        _ = a * (r * (star (aX i) * aX i * rX i + rX i)) := by
          noncomm_ring
        _ = a * (r * 1) := by rw [hri'']
        _ = a * r := by rw [mul_one]
    have htail :
        -(a * (r * (star a * (a * rX i)))) + a * rX i = a * (r * rX i) := by
      calc
        _ = a * ((1 - r * star a * a) * rX i) := by noncomm_ring
        _ = a * (r * rX i) := by rw [hra'']
    calc
      a * r - aX i * rX i = -(aX i * rX i) + a * r := by noncomm_ring
      _ = -(aX i * rX i) +
          (a * (r * (star (aX i) * (aX i * rX i))) + a * (r * rX i)) := by
        rw [hhead]
      _ = -(aX i * rX i) +
          (a * (r * (star (aX i) * (aX i * rX i))) +
            (-(a * (r * (star a * (a * rX i)))) + a * rX i)) := by
        rw [htail]
      _ = _ := by noncomm_ring
  have hraw : Tendsto (fun i ↦ Predual.equivDual (𝕜 := ℂ) (M := M) (P := P)
      (aX i * rX i) p.1) l
      (nhds (Predual.equivDual (𝕜 := ℂ) (M := M) (P := P) (a * r) p.1)) := by
    have hconst : Tendsto (fun _ : X ↦
        Predual.equivDual (𝕜 := ℂ) (M := M) (P := P) (a * r) p.1) l
        (nhds (Predual.equivDual (𝕜 := ℂ) (M := M) (P := P) (a * r) p.1)) :=
      tendsto_const_nhds
    have h := hconst.sub ht'
    rw [sub_zero] at h
    exact h.congr' (.of_forall fun _ ↦ by simp)
  have hscaled := (continuous_const_smul (2 : ℂ)).tendsto
    (Predual.equivDual (𝕜 := ℂ) (M := M) (P := P) (a * r) p.1) |>.comp hraw
  have hscaled' : Tendsto (fun i ↦ (2 : ℂ) •
      Predual.equivDual (𝕜 := ℂ) (M := M) (P := P) (aX i * rX i) p.1) l
      (nhds ((2 : ℂ) •
        Predual.equivDual (𝕜 := ℂ) (M := M) (P := P) (a * r) p.1)) := by
    exact hscaled.congr' (.of_forall fun _ ↦ rfl)
  simpa [CStarAlgebra.kaplanskyTransform, map_nsmul, aX, a, rX, r, two_smul, two_mul]
    using hscaled'

/-- On a norm-bounded family, convergence against a norm-dense invariant test space upgrades to
ultraweak convergence against the entire specified predual. -/
theorem tendsto_toUltraweak_of_tendsto_testPairing {V : Submodule ℂ P}
    (hV : SakaiInvariantTestSpace (M := M) V) {X : Type*} {l : Filter X}
    {u : X → M} {x : M} {C : ℝ} (hC : 0 ≤ C) (hu : ∀ᶠ i in l, ‖u i‖ ≤ C)
    (hlim : Tendsto
      (fun i ↦ show WeakBilin (testPairing (M := M) V) from u i) l
      (nhds (show WeakBilin (testPairing (M := M) V) from x))) :
    Tendsto (fun i ↦ toUltraweak ℂ P (u i)) l (nhds (toUltraweak ℂ P x)) := by
  have hDense : DenseRange (V.subtypeL : V →L[ℂ] P) := by
    change Dense (Set.range fun p : V ↦ (p : P))
    rw [show Set.range (fun p : V ↦ (p : P)) = (V : Set P) by ext; simp]
    exact hV.dense
  have h := WeakBilin.tendsto_of_denseRange_of_eventually_norm_le
    (B := normPairing (M := M) (P := P)) (T := V.subtypeL) hDense
    (Predual.equivDual (𝕜 := ℂ) (M := M) (P := P)).injective hC hu hlim
  exact h

/-- The identity from the test-space weak topology to the ultraweak topology is continuous on
each norm-closed ball. -/
theorem continuousOn_toUltraweak_closedBall {V : Submodule ℂ P}
    (hV : SakaiInvariantTestSpace (M := M) V) (C : ℝ) (hC : 0 ≤ C) :
    ContinuousOn
      (fun x : WeakBilin (testPairing (M := M) V) ↦
        toUltraweak ℂ P (WeakBilin.linearEquiv ℂ (testPairing (M := M) V) x))
      ((WeakBilin.linearEquiv ℂ (testPairing (M := M) V)) ⁻¹'
        Metric.closedBall (0 : M) C) := by
  intro x hx
  apply tendsto_toUltraweak_of_tendsto_testPairing hV hC
  · filter_upwards [self_mem_nhdsWithin] with y hy
    change WeakBilin.linearEquiv ℂ (testPairing (M := M) V) y ∈
      Metric.closedBall (0 : M) C at hy
    simpa only [Metric.mem_closedBall, dist_zero_right] using hy
  · exact tendsto_id.mono_left inf_le_left

/-- The canonical algebraic identification of Sakai's Mackey realization with the weak
realization induced by the same test space. -/
noncomputable def mackeyToWeakEquiv {V : Submodule ℂ P} :
    SakaiMackey (M := M) V ≃ₗ[ℂ] WeakBilin (testPairing (M := M) V) :=
  ofMackey ≪≫ₗ (WeakBilin.linearEquiv ℂ (testPairing (M := M) V)).symm

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace P] in
@[simp]
lemma mackeyToWeakEquiv_apply {V : Submodule ℂ P} (x : SakaiMackey (M := M) V) :
    mackeyToWeakEquiv x =
      (WeakBilin.linearEquiv ℂ (testPairing (M := M) V)).symm (ofMackey x) :=
  rfl

/-- Weak and Mackey topologies associated to the same separating test pairing have identical
closures of real-convex sets.  This is an application of Mathlib's compatible-dual closure
theorem. -/
theorem image_closure_mackeyToWeakEquiv {V : Submodule ℂ P}
    (_hV : SakaiInvariantTestSpace (M := M) V)
    {S : Set (SakaiMackey (M := M) V)} (hS : Convex ℝ S) :
    mackeyToWeakEquiv (M := M) (P := P) '' closure S =
      closure (mackeyToWeakEquiv (M := M) (P := P) '' S) := by
  let BW := WeakBilin.pairing (testPairing (M := M) V)
  have hBWsep : BW.SeparatingRight := by
    intro p hp
    apply testPairing_flip_injective (M := M) V
    ext x
    change testPairing (M := M) V x p = testPairing (M := M) V x 0
    rw [map_zero]
    exact hp ((WeakBilin.linearEquiv ℂ (testPairing (M := M) V)).symm x)
  letI : T1Space (WeakBilin (testPairing (M := M) V)) :=
    (WeakBilin.isEmbedding (testPairing_injective (M := M) _hV)).t1Space
  letI : BW.IsCompatibleDual :=
    LinearEquiv.IsCompatibleDual BW (LinearMap.IsWeak.rightDualEquiv BW hBWsep) (by
      ext p x
      rfl)
  letI : Module ℝ M := RestrictScalars.module ℝ ℂ M
  letI : IsScalarTower ℝ ℂ M := RestrictScalars.isScalarTower ℝ ℂ M
  letI : Module ℝ (SakaiMackey (M := M) V) :=
    RestrictScalars.module ℝ ℂ (SakaiMackey (M := M) V)
  letI : IsScalarTower ℝ ℂ (SakaiMackey (M := M) V) :=
    RestrictScalars.isScalarTower ℝ ℂ (SakaiMackey (M := M) V)
  letI : Module ℝ (WeakBilin (testPairing (M := M) V)) :=
    RestrictScalars.module ℝ ℂ (WeakBilin (testPairing (M := M) V))
  letI : IsScalarTower ℝ ℂ (WeakBilin (testPairing (M := M) V)) :=
    RestrictScalars.isScalarTower ℝ ℂ (WeakBilin (testPairing (M := M) V))
  letI : Module ℝ (WeakTestSpace (M := M) V) :=
    RestrictScalars.module ℝ ℂ (WeakTestSpace (M := M) V)
  letI : IsScalarTower ℝ ℂ (WeakTestSpace (M := M) V) :=
    RestrictScalars.isScalarTower ℝ ℂ (WeakTestSpace (M := M) V)
  letI : ContinuousSMul ℂ (SakaiMackey (M := M) V) := by
    apply PolarTopology.continuousSMul
    exact fun _ h ↦ h.1.isVonNBounded ℂ
  let BM := (PolarTopology.bilin (mackeyTestPairing (M := M) V)
    {s | IsCompact s ∧ AbsConvex ℂ s}).flip
  letI : BM.IsCompatibleDual := by
    dsimp only [BM]
    constructor
    · exact Mackey.range_coeLM_eq_range_bilin (mackeyTestPairing (M := M) V)
    · letI := LinearMap.IsWeak.isTopologicalAddGroup
          (mackeyTestPairing (M := M) V).flip
      rw [LinearMap.flip_flip, ← LinearMap.ker_eq_bot]
      ext x
      constructor
      · intro hx
        simp only [LinearMap.mem_ker, LinearMap.ext_iff, LinearMap.flip_apply,
          LinearEquiv.arrowCongr_apply, LinearEquiv.symm_symm, LinearEquiv.refl_apply,
          LinearMap.zero_apply, Submodule.mem_bot] at hx ⊢
        apply (LinearMap.flip_separatingLeft.mp <|
          LinearMap.IsWeak.separatingLeft_of_t1Space
            (mackeyTestPairing (M := M) V).flip) x
        exact hx
      · intro hx
        simp at hx
        aesop
  letI : LocallyConvexSpace ℝ (SakaiMackey (M := M) V) := by
    let _ := LinearMap.IsWeak.isTopologicalAddGroup
      (mackeyTestPairing (M := M) V).flip
    let _ := LinearMap.IsWeak.continuousSMul
      (mackeyTestPairing (M := M) V).flip
    exact PolarTopology.locallyConvexSpace
      (nonempty_setOf_isCompact_absConvex ℂ _)
      (directedOn_setOf_isCompact_absConvex ℂ _)
      fun _ h ↦ h.1.isVonNBounded ℂ
  letI : LocallyConvexSpace ℝ (WeakBilin (testPairing (M := M) V)) :=
    WeakBilin.locallyConvexSpace
  let hBM : BM.IsCompatibleDual := inferInstance
  let eDual : StrongDual ℂ (WeakBilin (testPairing (M := M) V)) ≃ₗ[ℂ]
      StrongDual ℂ (SakaiMackey (M := M) V) :=
    (LinearMap.IsCompatibleDual.equiv BW).symm ≪≫ₗ
      (WeakBilin.linearEquiv ℂ (testPairing (M := M) V).flip).symm ≪≫ₗ
        LinearMap.IsCompatibleDual.equiv (h := hBM) BM
  apply LinearEquiv.image_closure_of_convex' hS mackeyToWeakEquiv eDual
  intro f
  ext x
  let p : V := (LinearMap.IsCompatibleDual.equiv BW).symm f
  have hp : BW (mackeyToWeakEquiv (M := M) (P := P) x) p =
      f (mackeyToWeakEquiv (M := M) (P := P) x) := by
    calc
      _ = (LinearMap.IsCompatibleDual.equiv BW p)
          (mackeyToWeakEquiv (M := M) (P := P) x) :=
        (LinearMap.IsCompatibleDual.equiv_apply_apply BW p _).symm
      _ = _ := by rw [(LinearMap.IsCompatibleDual.equiv BW).apply_symm_apply f]
  change mackeyTestPairing (M := M) V (ofMackey x)
      ((WeakBilin.linearEquiv ℂ (testPairing (M := M) V).flip).symm p) =
    f (mackeyToWeakEquiv (M := M) (P := P) x)
  exact hp

/-- Sakai's contraction transform is continuous from `τ(M,V)` to `σ(M,V)`. -/
theorem continuous_kaplanskyTransform {V : Submodule ℂ P}
    (hV : SakaiInvariantTestSpace (M := M) V) :
    Continuous (fun x : SakaiMackey (M := M) V ↦
      show WeakBilin (testPairing (M := M) V) from
        CStarAlgebra.kaplanskyTransform (A := M) (ofMackey x)) := by
  rw [continuous_iff_continuousAt]
  intro x
  exact tendsto_kaplanskyTransform hV tendsto_id

/-- The Kaplansky transform of every ambient element belongs to the ultraweak closure of the
unit ball of a norm-closed, test-weakly dense star subalgebra. -/
theorem kaplanskyTransform_mem_ultraweak_closure {V : Submodule ℂ P}
    (hV : SakaiInvariantTestSpace (M := M) V)
    (S : NonUnitalStarSubalgebra ℂ M) [IsClosed (S : Set M)]
    (hS : Dense ((WeakBilin.linearEquiv ℂ (testPairing (M := M) V)) ⁻¹' (S : Set M)))
    (a : M) :
    toUltraweak ℂ P (CStarAlgebra.kaplanskyTransform a) ∈
      closure (ofUltraweak ⁻¹' ((S : Set M) ∩ Metric.closedBall (0 : M) 1)) := by
  let SM : Set (SakaiMackey (M := M) V) := ofMackey ⁻¹' (S : Set M)
  let SW : Set (WeakBilin (testPairing (M := M) V)) :=
    (WeakBilin.linearEquiv ℂ (testPairing (M := M) V)) ⁻¹' (S : Set M)
  let CW : Set (WeakBilin (testPairing (M := M) V)) :=
    (WeakBilin.linearEquiv ℂ (testPairing (M := M) V)) ⁻¹'
      ((S : Set M) ∩ Metric.closedBall (0 : M) 1)
  let CU : Set σ(M, P) :=
    ofUltraweak ⁻¹' ((S : Set M) ∩ Metric.closedBall (0 : M) 1)
  have hSMconv : Convex ℝ SM := by
    let SR := S.toNonUnitalSubalgebra.toSubmodule.restrictScalars ℝ
    change Convex ℝ ((ofMackey.restrictScalars ℝ).toLinearMap ⁻¹' (SR : Set M))
    exact SR.convex.linear_preimage (ofMackey.restrictScalars ℝ).toLinearMap
  have himage : mackeyToWeakEquiv (M := M) (P := P) '' SM = SW := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      refine ⟨toMackey (mackeyTestPairing (M := M) V)
        (WeakBilin.linearEquiv ℂ (testPairing (M := M) V) x), ?_, ?_⟩
      · exact hx
      · apply (WeakBilin.linearEquiv ℂ (testPairing (M := M) V)).injective
        change ofMackey (toMackey (mackeyTestPairing (M := M) V)
          (WeakBilin.linearEquiv ℂ (testPairing (M := M) V) x)) =
            WeakBilin.linearEquiv ℂ (testPairing (M := M) V) x
        exact ofMackey_toMackey _
  have hSMdense : closure SM = Set.univ := by
    have himageClosure := image_closure_mackeyToWeakEquiv hV hSMconv
    rw [himage, hS.closure_eq] at himageClosure
    apply Set.eq_univ_of_forall
    intro x
    have hx : mackeyToWeakEquiv (M := M) (P := P) x ∈
        mackeyToWeakEquiv (M := M) (P := P) '' closure SM := by
      rw [himageClosure]
      trivial
    obtain ⟨y, hy, hxy⟩ := hx
    exact (mackeyToWeakEquiv (M := M) (P := P)).injective hxy |>.symm ▸ hy
  have haM : toMackey (mackeyTestPairing (M := M) V) a ∈ closure SM := by
    rw [hSMdense]
    trivial
  have hmaps : Set.MapsTo
      (fun x : SakaiMackey (M := M) V ↦
        show WeakBilin (testPairing (M := M) V) from
          CStarAlgebra.kaplanskyTransform (A := M) (ofMackey x)) SM CW := by
    intro x hx
    exact ⟨CStarAlgebra.kaplanskyTransform_mem_nonUnitalStarSubalgebra S hx,
      CStarAlgebra.kaplanskyTransform_mem_closedBall (ofMackey x)⟩
  have haW : (show WeakBilin (testPairing (M := M) V) from
      CStarAlgebra.kaplanskyTransform (A := M) a) ∈ closure CW := by
    simpa only [ofMackey_toMackey] using
      (continuous_kaplanskyTransform hV).continuousAt.continuousWithinAt.mem_closure haM hmaps
  have hball : (show WeakBilin (testPairing (M := M) V) from
      CStarAlgebra.kaplanskyTransform (A := M) a) ∈
      (WeakBilin.linearEquiv ℂ (testPairing (M := M) V)) ⁻¹'
        Metric.closedBall (0 : M) 1 :=
    CStarAlgebra.kaplanskyTransform_mem_closedBall a
  have hcont := continuousOn_toUltraweak_closedBall hV 1 zero_le_one _ hball
  have hCWball : CW ⊆
      (WeakBilin.linearEquiv ℂ (testPairing (M := M) V)) ⁻¹'
        Metric.closedBall (0 : M) 1 := fun _ hx ↦ hx.2
  have hCWCU : Set.MapsTo
      (fun x : WeakBilin (testPairing (M := M) V) ↦
        toUltraweak ℂ P (WeakBilin.linearEquiv ℂ (testPairing (M := M) V) x))
      CW CU := fun _ hx ↦ hx
  exact hcont.mono hCWball |>.mem_closure haW hCWCU

/-- The ultraweak closure of the unit ball of a norm-closed, test-weakly dense star subalgebra is
the ambient unit ball.  The proof is the Krein--Milman step in Sakai's argument. -/
theorem ultraweak_closure_closed_subalgebra_unitBall {V : Submodule ℂ P}
    (hV : SakaiInvariantTestSpace (M := M) V)
    (S : NonUnitalStarSubalgebra ℂ M) [IsClosed (S : Set M)]
    (hS : Dense ((WeakBilin.linearEquiv ℂ (testPairing (M := M) V)) ⁻¹' (S : Set M))) :
    closure (ofUltraweak ⁻¹' ((S : Set M) ∩ Metric.closedBall (0 : M) 1) : Set σ(M, P)) =
      (ofUltraweak ⁻¹' Metric.closedBall (0 : M) 1 : Set σ(M, P)) := by
  let C : Set σ(M, P) :=
    ofUltraweak ⁻¹' ((S : Set M) ∩ Metric.closedBall (0 : M) 1)
  let B : Set σ(M, P) := ofUltraweak ⁻¹' Metric.closedBall (0 : M) 1
  letI : Module ℝ M := RestrictScalars.module ℝ ℂ M
  letI : IsScalarTower ℝ ℂ M := RestrictScalars.isScalarTower ℝ ℂ M
  letI : Module ℝ σ(M, P) := RestrictScalars.module ℝ ℂ σ(M, P)
  letI : IsScalarTower ℝ ℂ σ(M, P) := RestrictScalars.isScalarTower ℝ ℂ σ(M, P)
  letI : LocallyConvexSpace ℝ σ(M, P) := WeakBilin.locallyConvexSpace
  have hBcompact : IsCompact B := Ultraweak.isCompact_closedBall ℂ P (0 : M) 1
  have hBconv : Convex ℝ B := by
    exact (convex_closedBall (0 : M) 1).linear_preimage
      ((Ultraweak.linearEquiv ℂ M P).restrictScalars ℝ).toLinearMap
  have hCconv : Convex ℝ C := by
    let SR := S.toNonUnitalSubalgebra.toSubmodule.restrictScalars ℝ
    have hSint : Convex ℝ ((S : Set M) ∩ Metric.closedBall (0 : M) 1) := by
      exact SR.convex.inter (convex_closedBall (0 : M) 1)
    exact hSint.linear_preimage
      ((Ultraweak.linearEquiv ℂ M P).restrictScalars ℝ).toLinearMap
  have hExtreme : B.extremePoints ℝ ⊆ closure C := by
    intro x hx
    let e : σ(M, P) ≃ₗ[ℝ] M := (Ultraweak.linearEquiv ℂ M P).restrictScalars ℝ
    have heB : e '' B = Metric.closedBall (0 : M) 1 := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · intro hy
        exact ⟨e.symm y, hy, e.apply_symm_apply y⟩
    have hex : ofUltraweak x ∈
        (Metric.closedBall (0 : M) 1).extremePoints ℝ := by
      have hx' : e x ∈ e '' B.extremePoints ℝ := ⟨x, hx, rfl⟩
      rw [image_extremePoints, heB] at hx'
      exact hx'
    have hmem := kaplanskyTransform_mem_ultraweak_closure hV S hS (ofUltraweak x)
    rw [CStarAlgebra.kaplanskyTransform_eq_self_of_mem_extremePoints_unitClosedBall hex] at hmem
    exact hmem
  apply Set.Subset.antisymm
  · exact closure_minimal (fun _ hx ↦ hx.2) hBcompact.isClosed
  · change B ⊆ closure C
    rw [← closure_convexHull_extremePoints hBcompact hBconv]
    have hclosureConv : Convex ℝ (closure C) := hCconv.closure
    have hhull : convexHull ℝ (B.extremePoints ℝ) ⊆ closure C :=
      convexHull_min hExtreme hclosureConv
    simpa only [closure_closure] using closure_mono hhull

/-- The ultraweak closure of the unit ball of a test-weakly dense star subalgebra is the ambient
unit ball.  The nonclosed case follows from the closed case by the general convex-set fact that
closure commutes with intersection with a positive-radius ball centered in the set. -/
theorem ultraweak_closure_subalgebra_unitBall {V : Submodule ℂ P}
    (hV : SakaiInvariantTestSpace (M := M) V)
    (S : NonUnitalStarSubalgebra ℂ M)
    (hS : Dense ((WeakBilin.linearEquiv ℂ (testPairing (M := M) V)) ⁻¹' (S : Set M))) :
    closure (ofUltraweak ⁻¹' ((S : Set M) ∩ Metric.closedBall (0 : M) 1) : Set σ(M, P)) =
      (ofUltraweak ⁻¹' Metric.closedBall (0 : M) 1 : Set σ(M, P)) := by
  let T := S.topologicalClosure
  letI : IsClosed (T : Set M) := S.isClosed_topologicalClosure
  have hT : Dense ((WeakBilin.linearEquiv ℂ (testPairing (M := M) V)) ⁻¹' (T : Set M)) :=
    hS.mono fun _ hx ↦ S.le_topologicalClosure hx
  have hrealconv : Convex ℝ (S : Set M) :=
    (S.toNonUnitalSubalgebra.toSubmodule.restrictScalars ℝ).convex
  have hnormClosure :
      closure ((S : Set M) ∩ Metric.closedBall (0 : M) 1) =
        (T : Set M) ∩ Metric.closedBall (0 : M) 1 := by
    change closure ((S : Set M) ∩ Metric.closedBall (0 : M) 1) =
      closure (S : Set M) ∩ Metric.closedBall (0 : M) 1
    exact hrealconv.closure_inter_unitClosedBall S.zero_mem
  have hTU :
      (ofUltraweak ⁻¹' ((T : Set M) ∩ Metric.closedBall (0 : M) 1) : Set σ(M, P)) ⊆
        closure (ofUltraweak ⁻¹' ((S : Set M) ∩ Metric.closedBall (0 : M) 1) :
          Set σ(M, P)) := by
    intro x hx
    have hxnorm : ofUltraweak x ∈
        closure ((S : Set M) ∩ Metric.closedBall (0 : M) 1) := by
      rw [hnormClosure]
      exact hx
    have hmap := map_mem_closure (continuous_toUltraweak (𝕜 := ℂ) (M := M) (P := P))
      hxnorm (t := ofUltraweak ⁻¹' ((S : Set M) ∩ Metric.closedBall (0 : M) 1)) (by
        intro y hy
        simpa using hy)
    simpa using hmap
  have hUW_T := ultraweak_closure_closed_subalgebra_unitBall hV T hT
  apply Set.Subset.antisymm
  · exact closure_minimal (fun _ hx ↦ hx.2) (Ultraweak.isClosed_closedBall ℂ P 0 1)
  · calc
      (ofUltraweak ⁻¹' Metric.closedBall (0 : M) 1 : Set σ(M, P)) =
          closure (ofUltraweak ⁻¹' ((T : Set M) ∩ Metric.closedBall (0 : M) 1) :
            Set σ(M, P)) := hUW_T.symm
      _ ⊆ closure (closure (ofUltraweak ⁻¹'
          ((S : Set M) ∩ Metric.closedBall (0 : M) 1) : Set σ(M, P))) := closure_mono hTU
      _ = closure (ofUltraweak ⁻¹' ((S : Set M) ∩ Metric.closedBall (0 : M) 1) :
          Set σ(M, P)) := closure_closure

/-- The weak realization obtained by taking the entire specified predual is canonically the
ultraweak topology. -/
noncomputable def topWeakUltraweakCLE :
    WeakBilin (testPairing (M := M) (⊤ : Submodule ℂ P)) ≃L[ℂ] σ(M, P) where
  toLinearEquiv :=
    WeakBilin.linearEquiv ℂ (testPairing (M := M) (⊤ : Submodule ℂ P)) ≪≫ₗ
      (Ultraweak.linearEquiv ℂ M P).symm
  continuous_toFun := by
    apply Ultraweak.continuous_of_continuous_eval
    intro p
    convert WeakBilin.eval_continuous
      (testPairing (M := M) (⊤ : Submodule ℂ P)) ⟨p, Submodule.mem_top⟩ using 1
    funext x
    rfl
  continuous_invFun := by
    apply WeakBilin.continuous_of_continuous_eval
    intro p
    convert Ultraweak.eval_continuous (M := M) (P := P) p.1 using 1
    funext x
    rfl

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace P] in
@[simp]
lemma ofUltraweak_topWeakUltraweakCLE
    (x : WeakBilin (testPairing (M := M) (⊤ : Submodule ℂ P))) :
    ofUltraweak (topWeakUltraweakCLE (M := M) (P := P) x) =
      WeakBilin.linearEquiv ℂ (testPairing (M := M) (⊤ : Submodule ℂ P)) x :=
  rfl

/-- Convex unit-ball density transfers from the ultraweak topology to the Mackey topology of the
specified predual.  This is the topology-independent last step in Kaplansky density arguments. -/
theorem mackey_closure_unitBall_of_ultraweak_closure (C₀ : Set M)
    (hC₀ : Convex ℝ C₀)
    (hUW : closure (ofUltraweak ⁻¹' C₀ : Set σ(M, P)) =
      (ofUltraweak ⁻¹' Metric.closedBall (0 : M) 1 : Set σ(M, P))) :
    closure (ofMackey ⁻¹' C₀ :
        Set (SakaiMackey (M := M) (⊤ : Submodule ℂ P))) =
      (ofMackey ⁻¹' Metric.closedBall (0 : M) 1 :
        Set (SakaiMackey (M := M) (⊤ : Submodule ℂ P))) := by
  let CM : Set (SakaiMackey (M := M) (⊤ : Submodule ℂ P)) :=
    ofMackey ⁻¹' C₀
  let BM : Set (SakaiMackey (M := M) (⊤ : Submodule ℂ P)) :=
    ofMackey ⁻¹' Metric.closedBall (0 : M) 1
  let CW : Set (WeakBilin (testPairing (M := M) (⊤ : Submodule ℂ P))) :=
    (WeakBilin.linearEquiv ℂ (testPairing (M := M) (⊤ : Submodule ℂ P))) ⁻¹'
      C₀
  let BW : Set (WeakBilin (testPairing (M := M) (⊤ : Submodule ℂ P))) :=
    (WeakBilin.linearEquiv ℂ (testPairing (M := M) (⊤ : Submodule ℂ P))) ⁻¹'
      Metric.closedBall (0 : M) 1
  let CU : Set σ(M, P) :=
    ofUltraweak ⁻¹' C₀
  let BU : Set σ(M, P) := ofUltraweak ⁻¹' Metric.closedBall (0 : M) 1
  have hCMconv : Convex ℝ CM := by
    exact hC₀.linear_preimage (ofMackey.restrictScalars ℝ).toLinearMap
  have hMCimage : mackeyToWeakEquiv (M := M) (P := P) '' CM = CW := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      refine ⟨toMackey (mackeyTestPairing (M := M) (⊤ : Submodule ℂ P))
        (WeakBilin.linearEquiv ℂ
          (testPairing (M := M) (⊤ : Submodule ℂ P)) x), hx, ?_⟩
      apply (WeakBilin.linearEquiv ℂ
        (testPairing (M := M) (⊤ : Submodule ℂ P))).injective
      change ofMackey (toMackey (mackeyTestPairing (M := M) (⊤ : Submodule ℂ P))
        (WeakBilin.linearEquiv ℂ
          (testPairing (M := M) (⊤ : Submodule ℂ P)) x)) = _
      exact ofMackey_toMackey _
  have hMBimage : mackeyToWeakEquiv (M := M) (P := P) '' BM = BW := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      refine ⟨toMackey (mackeyTestPairing (M := M) (⊤ : Submodule ℂ P))
        (WeakBilin.linearEquiv ℂ
          (testPairing (M := M) (⊤ : Submodule ℂ P)) x), hx, ?_⟩
      apply (WeakBilin.linearEquiv ℂ
        (testPairing (M := M) (⊤ : Submodule ℂ P))).injective
      change ofMackey (toMackey (mackeyTestPairing (M := M) (⊤ : Submodule ℂ P))
        (WeakBilin.linearEquiv ℂ
          (testPairing (M := M) (⊤ : Submodule ℂ P)) x)) = _
      exact ofMackey_toMackey _
  have hWU_C : topWeakUltraweakCLE (M := M) (P := P) '' CW = CU := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨(topWeakUltraweakCLE (M := M) (P := P)).symm x, hx,
        (topWeakUltraweakCLE (M := M) (P := P)).apply_symm_apply x⟩
  have hWU_B : topWeakUltraweakCLE (M := M) (P := P) '' BW = BU := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨(topWeakUltraweakCLE (M := M) (P := P)).symm x, hx,
        (topWeakUltraweakCLE (M := M) (P := P)).apply_symm_apply x⟩
  have hW : closure CW = BW := by
    apply (topWeakUltraweakCLE (M := M) (P := P)).injective.image_injective
    rw [(topWeakUltraweakCLE (M := M) (P := P)).image_closure, hWU_C, hUW, hWU_B]
  have hMimage := image_closure_mackeyToWeakEquiv
    (SakaiInvariantTestSpace.top (M := M) (P := P)) hCMconv
  rw [hMCimage, hW] at hMimage
  change closure CM = BM
  apply (mackeyToWeakEquiv (M := M) (P := P)).injective.image_injective
  exact hMimage.trans hMBimage.symm

/-- **Sakai's density theorem, Theorem 1.9.1**, for a norm-closed star subalgebra: the
subalgebra's unit ball is dense in the ambient unit ball for the Mackey topology of the specified
predual. -/
theorem kaplansky_density_closed_Sak_1_9_1 {V : Submodule ℂ P}
    (hV : SakaiInvariantTestSpace (M := M) V)
    (S : NonUnitalStarSubalgebra ℂ M) [IsClosed (S : Set M)]
    (hS : Dense ((WeakBilin.linearEquiv ℂ (testPairing (M := M) V)) ⁻¹' (S : Set M))) :
    closure (ofMackey ⁻¹' ((S : Set M) ∩ Metric.closedBall (0 : M) 1) :
        Set (SakaiMackey (M := M) (⊤ : Submodule ℂ P))) =
      (ofMackey ⁻¹' Metric.closedBall (0 : M) 1 :
        Set (SakaiMackey (M := M) (⊤ : Submodule ℂ P))) := by
  apply mackey_closure_unitBall_of_ultraweak_closure
  · exact (S.toNonUnitalSubalgebra.toSubmodule.restrictScalars ℝ).convex.inter
      (convex_closedBall (0 : M) 1)
  · exact ultraweak_closure_closed_subalgebra_unitBall hV S hS

/-- **Sakai's density theorem, Theorem 1.9.1**: the unit ball of a test-weakly dense
self-adjoint subalgebra is dense in the ambient unit ball for the Mackey topology of the specified
predual. -/
theorem kaplansky_density_Sak_1_9_1 {V : Submodule ℂ P}
    (hV : SakaiInvariantTestSpace (M := M) V)
    (S : NonUnitalStarSubalgebra ℂ M)
    (hS : Dense ((WeakBilin.linearEquiv ℂ (testPairing (M := M) V)) ⁻¹' (S : Set M))) :
    closure (ofMackey ⁻¹' ((S : Set M) ∩ Metric.closedBall (0 : M) 1) :
        Set (SakaiMackey (M := M) (⊤ : Submodule ℂ P))) =
      (ofMackey ⁻¹' Metric.closedBall (0 : M) 1 :
        Set (SakaiMackey (M := M) (⊤ : Submodule ℂ P))) := by
  have hrealconv : Convex ℝ (S : Set M) :=
    (S.toNonUnitalSubalgebra.toSubmodule.restrictScalars ℝ).convex
  exact mackey_closure_unitBall_of_ultraweak_closure
    ((S : Set M) ∩ Metric.closedBall (0 : M) 1)
    (hrealconv.inter (convex_closedBall (0 : M) 1))
    (ultraweak_closure_subalgebra_unitBall hV S hS)

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace P] in
/-- Ultraweak density implies density for the canonically equivalent weak topology obtained by
taking the whole specified predual as test space. -/
theorem dense_topWeak_of_ultraweak (S : Set M)
    (hS : Dense (ofUltraweak ⁻¹' S : Set σ(M, P))) :
    Dense ((WeakBilin.linearEquiv ℂ
      (testPairing (M := M) (⊤ : Submodule ℂ P))) ⁻¹' S) := by
  have hdense := hS.preimage (topWeakUltraweakCLE (M := M) (P := P)).isOpenMap
  simpa only [preimage_preimage, ofUltraweak_topWeakUltraweakCLE] using hdense

/-- Kaplansky density for an ultraweakly dense self-adjoint subalgebra: its unit ball is dense in
the ambient unit ball for the Mackey topology of the specified predual. -/
theorem kaplansky_density_ultraweak (S : NonUnitalStarSubalgebra ℂ M)
    (hS : Dense (ofUltraweak ⁻¹' (S : Set M) : Set σ(M, P))) :
    closure (ofMackey ⁻¹' ((S : Set M) ∩ Metric.closedBall (0 : M) 1) :
        Set (SakaiMackey (M := M) (⊤ : Submodule ℂ P))) =
      (ofMackey ⁻¹' Metric.closedBall (0 : M) 1 :
        Set (SakaiMackey (M := M) (⊤ : Submodule ℂ P))) :=
  kaplansky_density_Sak_1_9_1 (SakaiInvariantTestSpace.top (M := M) (P := P)) S
    (dense_topWeak_of_ultraweak (M := M) (P := P) (S : Set M) hS)

end SakaiInvariantTestSpace

end RestrictedPairing

end Ultraweak
