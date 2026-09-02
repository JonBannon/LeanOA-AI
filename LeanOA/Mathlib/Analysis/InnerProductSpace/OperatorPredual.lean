module

public import LeanOA.Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# The norm-closed vector-functional predual of bounded operators

For a seminormed space `E` and a Hilbert space `F`, this file takes the norm closure of the
finite span of the vector functionals

`T ↦ ⟪η, T ξ⟫_𝕜`

inside the norm dual of `E →L[𝕜] F`.  When `F` is complete, canonical evaluation identifies
`E →L[𝕜] F` linearly and isometrically with the full dual of that closure.

The construction is more general than the endomorphism case needed for `B(H)`.  Surjectivity is
proved by turning a functional on the closure into a bounded conjugate-linear map
`E →L⋆[𝕜] StrongDual 𝕜 F`, then composing it with the conjugate-linear
Fréchet--Riesz equivalence.  Agreement on vector functionals extends first over their algebraic
span and then over its norm closure.
-/

@[expose] public section

open scoped InnerProduct InnerProductSpace

noncomputable section

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/- The nested continuous-dual/submodule type needs one more synthesis layer than the project-wide
Mathlib-compatible default.  This is an elaboration setting only; no competing instances are
introduced. -/
set_option maxSynthPendingDepth 4

/-! ## Coefficient norms -/

/-- The pointwise operator-norm estimate for a vector functional. -/
lemma norm_vectorFunctional_apply_le (xi : E) (eta : F) (T : E →L[𝕜] F) :
    ‖vectorFunctional xi eta T‖ ≤ ‖T‖ * ‖xi‖ * ‖eta‖ := by
  rw [vectorFunctional_apply]
  calc
    ‖⟪eta, T xi⟫_𝕜‖ ≤ ‖eta‖ * ‖T xi‖ := norm_inner_le_norm _ _
    _ ≤ ‖eta‖ * (‖T‖ * ‖xi‖) := by
      gcongr
      exact T.le_opNorm xi
    _ = ‖T‖ * ‖xi‖ * ‖eta‖ := by ring

/-- A vector functional has norm equal to the product of the norms of its two vectors.  This
includes zero and non-Hausdorff seminormed domains, so no nontriviality assumption is needed. -/
@[simp]
theorem norm_vectorFunctional (xi : E) (eta : F) :
    ‖vectorFunctional (𝕜 := 𝕜) xi eta‖ = ‖xi‖ * ‖eta‖ := by
  apply le_antisymm
  · apply (vectorFunctional (𝕜 := 𝕜) xi eta).opNorm_le_bound
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    intro T
    calc
      ‖vectorFunctional xi eta T‖ ≤ ‖T‖ * ‖xi‖ * ‖eta‖ :=
        norm_vectorFunctional_apply_le xi eta T
      _ = (‖xi‖ * ‖eta‖) * ‖T‖ := by ring
  · by_cases heta : eta = 0
    · simp [heta]
    have heta_norm : 0 < ‖eta‖ := norm_pos_iff.mpr heta
    obtain ⟨g, hg_norm, hg_apply⟩ := exists_dual_vector'' 𝕜 xi
    let T : E →L[𝕜] F := ContinuousLinearMap.smulRight g eta
    have hT_norm : ‖T‖ ≤ ‖eta‖ := by
      rw [show ‖T‖ = ‖g‖ * ‖eta‖ by
        simp [T, ContinuousLinearMap.norm_smulRight_apply]]
      simpa using mul_le_mul_of_nonneg_right hg_norm (norm_nonneg eta)
    have hmul : (‖xi‖ * ‖eta‖) * ‖eta‖ ≤
        ‖vectorFunctional (𝕜 := 𝕜) xi eta‖ * ‖eta‖ := by
      calc
        (‖xi‖ * ‖eta‖) * ‖eta‖ = ‖vectorFunctional (𝕜 := 𝕜) xi eta T‖ := by
          rw [vectorFunctional_apply]
          simp only [T, ContinuousLinearMap.smulRight_apply, hg_apply, inner_smul_right]
          rw [inner_self_eq_norm_sq_to_K]
          simp [norm_pow]
          ring
        _ ≤ ‖vectorFunctional (𝕜 := 𝕜) xi eta‖ * ‖T‖ :=
          (vectorFunctional (𝕜 := 𝕜) xi eta).le_opNorm T
        _ ≤ ‖vectorFunctional (𝕜 := 𝕜) xi eta‖ * ‖eta‖ := by gcongr
    nlinarith

/-! ## Norm closure and its dense algebraic core -/

/-- The norm closure of the algebraic span of the vector functionals on `E →L[𝕜] F`.  This is an
abbreviation so the standard submodule normed-space instances remain available downstream. -/
abbrev vectorFunctionalClosure : Submodule 𝕜 ((E →L[𝕜] F) →L[𝕜] 𝕜) :=
  (vectorFunctionalSpan (𝕜 := 𝕜) (E := E) (F := F)).topologicalClosure

instance vectorFunctionalClosure.instCompleteSpace :
    CompleteSpace (vectorFunctionalClosure (𝕜 := 𝕜) (E := E) (F := F)) :=
  Submodule.topologicalClosure.completeSpace _

/-- Every vector functional belongs to the norm-closed vector-functional space. -/
lemma vectorFunctional_mem_closure (xi : E) (eta : F) :
    vectorFunctional (𝕜 := 𝕜) xi eta ∈
      vectorFunctionalClosure (𝕜 := 𝕜) (E := E) (F := F) :=
  Submodule.le_topologicalClosure _ (vectorFunctional_mem_span xi eta)

/-- A vector functional, regarded as an element of the norm-closed vector-functional space. -/
def vectorFunctionalInClosure (xi : E) (eta : F) :
    vectorFunctionalClosure (𝕜 := 𝕜) (E := E) (F := F) :=
  ⟨vectorFunctional xi eta, vectorFunctional_mem_closure xi eta⟩

@[simp]
lemma coe_vectorFunctionalInClosure (xi : E) (eta : F) :
    (vectorFunctionalInClosure (𝕜 := 𝕜) xi eta :
      (E →L[𝕜] F) →L[𝕜] 𝕜) = vectorFunctional xi eta :=
  rfl

@[simp]
lemma vectorFunctionalInClosure_add_left (xi₁ xi₂ : E) (eta : F) :
    vectorFunctionalInClosure (𝕜 := 𝕜) (xi₁ + xi₂) eta =
      vectorFunctionalInClosure xi₁ eta + vectorFunctionalInClosure xi₂ eta := by
  ext T
  simp [vectorFunctionalInClosure, vectorFunctional_apply, inner_add_right]

@[simp]
lemma vectorFunctionalInClosure_smul_left (c : 𝕜) (xi : E) (eta : F) :
    vectorFunctionalInClosure (𝕜 := 𝕜) (c • xi) eta =
      c • vectorFunctionalInClosure xi eta := by
  ext T
  simp [vectorFunctionalInClosure, vectorFunctional_apply, inner_smul_right]

@[simp]
lemma vectorFunctionalInClosure_add_right (xi : E) (eta₁ eta₂ : F) :
    vectorFunctionalInClosure (𝕜 := 𝕜) xi (eta₁ + eta₂) =
      vectorFunctionalInClosure xi eta₁ + vectorFunctionalInClosure xi eta₂ := by
  ext T
  simp [vectorFunctionalInClosure, vectorFunctional_apply, inner_add_left]

@[simp]
lemma vectorFunctionalInClosure_smul_right (c : 𝕜) (xi : E) (eta : F) :
    vectorFunctionalInClosure (𝕜 := 𝕜) xi (c • eta) =
      star c • vectorFunctionalInClosure xi eta := by
  ext T
  simp [vectorFunctionalInClosure, vectorFunctional_apply, inner_smul_left]

@[simp]
lemma norm_vectorFunctionalInClosure (xi : E) (eta : F) :
    ‖vectorFunctionalInClosure (𝕜 := 𝕜) xi eta‖ = ‖xi‖ * ‖eta‖ :=
  norm_vectorFunctional xi eta

/-- The canonical isometric inclusion of the finite vector-functional span into its norm
closure. -/
def vectorFunctionalSpanToClosureₗᵢ :
    vectorFunctionalSpan (𝕜 := 𝕜) (E := E) (F := F) →ₗᵢ[𝕜]
      vectorFunctionalClosure (𝕜 := 𝕜) (E := E) (F := F) where
  toLinearMap := Submodule.inclusion (Submodule.le_topologicalClosure _)
  norm_map' _ := rfl

/-- The continuous-linear version of the inclusion of the finite vector-functional span into its
norm closure. -/
def vectorFunctionalSpanToClosure :
    vectorFunctionalSpan (𝕜 := 𝕜) (E := E) (F := F) →L[𝕜]
      vectorFunctionalClosure (𝕜 := 𝕜) (E := E) (F := F) :=
  vectorFunctionalSpanToClosureₗᵢ.toContinuousLinearMap

@[simp]
lemma vectorFunctionalSpanToClosure_apply
    (f : vectorFunctionalSpan (𝕜 := 𝕜) (E := E) (F := F)) :
    (vectorFunctionalSpanToClosure f : (E →L[𝕜] F) →L[𝕜] 𝕜) = f :=
  rfl

/-- The finite vector-functional span is norm dense in its defining closure. -/
theorem denseRange_vectorFunctionalSpanToClosure :
    DenseRange (vectorFunctionalSpanToClosure (𝕜 := 𝕜) (E := E) (F := F)) := by
  change DenseRange (Set.inclusion (Submodule.le_topologicalClosure
    (vectorFunctionalSpan (𝕜 := 𝕜) (E := E) (F := F))))
  rw [denseRange_inclusion_iff]
  intro f hf
  exact hf

/-! ## Canonical evaluation -/

/-- The algebraic evaluation pairing between an operator and the norm-closed vector-functional
space. -/
def vectorFunctionalClosurePairing :
    (E →L[𝕜] F) →ₗ[𝕜]
      vectorFunctionalClosure (𝕜 := 𝕜) (E := E) (F := F) →ₗ[𝕜] 𝕜 :=
  ((ContinuousLinearMap.coeLM 𝕜).comp
    (vectorFunctionalClosure (𝕜 := 𝕜) (E := E) (F := F)).subtype).flip

@[simp]
lemma vectorFunctionalClosurePairing_apply (T : E →L[𝕜] F)
    (f : vectorFunctionalClosure (𝕜 := 𝕜) (E := E) (F := F)) :
    vectorFunctionalClosurePairing T f = f.1 T :=
  rfl

/-- Canonical evaluation of an operator on the norm-closed vector-functional space. -/
def vectorFunctionalClosureEvaluation :
    (E →L[𝕜] F) →L[𝕜]
      StrongDual 𝕜 (vectorFunctionalClosure (𝕜 := 𝕜) (E := E) (F := F)) :=
  (vectorFunctionalClosurePairing (𝕜 := 𝕜) (E := E) (F := F)).mkContinuous₂ 1
    fun T f ↦ by
      simpa [mul_comm] using f.1.le_opNorm T

@[simp]
lemma vectorFunctionalClosureEvaluation_apply_apply (T : E →L[𝕜] F)
    (f : vectorFunctionalClosure (𝕜 := 𝕜) (E := E) (F := F)) :
    vectorFunctionalClosureEvaluation T f = f.1 T :=
  rfl

lemma norm_vectorFunctionalClosureEvaluation_le (T : E →L[𝕜] F) :
    ‖vectorFunctionalClosureEvaluation (𝕜 := 𝕜) T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro f
  simpa [mul_comm] using f.1.le_opNorm T

/-- Canonical evaluation on the norm-closed vector-functional space preserves operator norm. -/
@[simp]
theorem norm_vectorFunctionalClosureEvaluation (T : E →L[𝕜] F) :
    ‖vectorFunctionalClosureEvaluation (𝕜 := 𝕜) T‖ = ‖T‖ := by
  apply le_antisymm (norm_vectorFunctionalClosureEvaluation_le T)
  apply T.opNorm_le_bound (norm_nonneg _)
  intro xi
  by_cases hxi : T xi = 0
  · rw [hxi, norm_zero]
    positivity
  let f : vectorFunctionalClosure (𝕜 := 𝕜) (E := E) (F := F) :=
    vectorFunctionalInClosure xi (T xi)
  have hf : ‖f‖ = ‖xi‖ * ‖T xi‖ :=
    norm_vectorFunctionalInClosure xi (T xi)
  have heval : ‖vectorFunctionalClosureEvaluation (𝕜 := 𝕜) T f‖ = ‖T xi‖ ^ 2 := by
    rw [vectorFunctionalClosureEvaluation_apply_apply,
      show f.1 = vectorFunctional xi (T xi) from rfl, vectorFunctional_apply,
      inner_self_eq_norm_sq_to_K]
    simp [norm_pow]
  have hbound := (vectorFunctionalClosureEvaluation (𝕜 := 𝕜) T).le_opNorm f
  rw [heval, hf] at hbound
  have hpos : 0 < ‖T xi‖ := norm_pos_iff.mpr hxi
  nlinarith [norm_nonneg xi, norm_nonneg
    (vectorFunctionalClosureEvaluation (𝕜 := 𝕜) T)]

/-- Canonical evaluation as a linear isometric embedding into the dual of the norm-closed
vector-functional space. -/
def vectorFunctionalClosureEvaluationₗᵢ :
    (E →L[𝕜] F) →ₗᵢ[𝕜]
      StrongDual 𝕜 (vectorFunctionalClosure (𝕜 := 𝕜) (E := E) (F := F)) where
  toLinearMap := (vectorFunctionalClosureEvaluation
    (𝕜 := 𝕜) (E := E) (F := F)).toLinearMap
  norm_map' := norm_vectorFunctionalClosureEvaluation

section Complete

variable [CompleteSpace F]

/-! ## Recovery and surjectivity -/

/-- The bounded conjugate-linear form associated to a functional on the norm-closed
vector-functional space. -/
def vectorFunctionalClosureRecoveryForm
    (g : StrongDual 𝕜 (vectorFunctionalClosure (𝕜 := 𝕜) (E := E) (F := F))) :
    E →L⋆[𝕜] StrongDual 𝕜 F :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂'ₛₗ (starRingEnd 𝕜) (RingHom.id 𝕜)
      (fun xi eta ↦ star (g (vectorFunctionalInClosure (𝕜 := 𝕜) xi eta)))
      (by intros; simp)
      (by intros; simp)
      (by intros; simp)
      (by intros; simp))
    ‖g‖ fun xi eta ↦ by
      calc
        ‖star (g (vectorFunctionalInClosure (𝕜 := 𝕜) xi eta))‖ =
            ‖g (vectorFunctionalInClosure (𝕜 := 𝕜) xi eta)‖ := norm_star _
        _ ≤ ‖g‖ * ‖vectorFunctionalInClosure (𝕜 := 𝕜) xi eta‖ := g.le_opNorm _
        _ ≤ ‖g‖ * (‖xi‖ * ‖eta‖) := by
          gcongr
          exact (norm_vectorFunctionalInClosure xi eta).le
        _ = ‖g‖ * ‖xi‖ * ‖eta‖ := by ring

omit [CompleteSpace F] in
@[simp]
lemma vectorFunctionalClosureRecoveryForm_apply_apply
    (g : StrongDual 𝕜 (vectorFunctionalClosure (𝕜 := 𝕜) (E := E) (F := F)))
    (xi : E) (eta : F) :
    vectorFunctionalClosureRecoveryForm g xi eta =
      star (g (vectorFunctionalInClosure (𝕜 := 𝕜) xi eta)) :=
  rfl

/-- Recover a bounded operator from a functional on the norm-closed vector-functional space. -/
def vectorFunctionalClosureRecover
    (g : StrongDual 𝕜 (vectorFunctionalClosure (𝕜 := 𝕜) (E := E) (F := F))) :
    E →L[𝕜] F :=
  ContinuousLinearMap.compSL E (StrongDual 𝕜 F) F
    (starRingEnd 𝕜) (starRingEnd 𝕜)
    ((InnerProductSpace.toDual 𝕜 F).symm : StrongDual 𝕜 F →L⋆[𝕜] F)
    (vectorFunctionalClosureRecoveryForm g)

@[simp]
lemma vectorFunctionalClosureRecover_apply
    (g : StrongDual 𝕜 (vectorFunctionalClosure (𝕜 := 𝕜) (E := E) (F := F)))
    (xi : E) :
    vectorFunctionalClosureRecover g xi =
      (InnerProductSpace.toDual 𝕜 F).symm (vectorFunctionalClosureRecoveryForm g xi) :=
  rfl

/-- Recovery has the prescribed value on every generating vector functional. -/
theorem vectorFunctionalClosureRecover_vectorFunctional
    (g : StrongDual 𝕜 (vectorFunctionalClosure (𝕜 := 𝕜) (E := E) (F := F)))
    (xi : E) (eta : F) :
    vectorFunctional (𝕜 := 𝕜) xi eta (vectorFunctionalClosureRecover g) =
      g (vectorFunctionalInClosure (𝕜 := 𝕜) xi eta) := by
  rw [vectorFunctional_apply]
  calc
    ⟪eta, vectorFunctionalClosureRecover g xi⟫_𝕜 =
        star ⟪vectorFunctionalClosureRecover g xi, eta⟫_𝕜 := by
      exact (inner_conj_symm (𝕜 := 𝕜) eta (vectorFunctionalClosureRecover g xi)).symm
    _ = star (vectorFunctionalClosureRecoveryForm g xi eta) := by
      rw [vectorFunctionalClosureRecover_apply, InnerProductSpace.toDual_symm_apply]
    _ = g (vectorFunctionalInClosure (𝕜 := 𝕜) xi eta) := by simp

/-- Evaluating the recovered operator gives the original functional on the entire norm closure. -/
theorem vectorFunctionalClosureEvaluation_recover
    (g : StrongDual 𝕜 (vectorFunctionalClosure (𝕜 := 𝕜) (E := E) (F := F))) :
    vectorFunctionalClosureEvaluation (vectorFunctionalClosureRecover g) = g := by
  let S := vectorFunctionalSpan (𝕜 := 𝕜) (E := E) (F := F)
  let P := vectorFunctionalClosure (𝕜 := 𝕜) (E := E) (F := F)
  let i : S →L[𝕜] P :=
    vectorFunctionalSpanToClosure (𝕜 := 𝕜) (E := E) (F := F)
  have hi : DenseRange i := by
    simpa only [i, S, P] using
      (denseRange_vectorFunctionalSpanToClosure (𝕜 := 𝕜) (E := E) (F := F))
  have hcomp :
      (fun p : P ↦ vectorFunctionalClosureEvaluation
          (vectorFunctionalClosureRecover g) p) ∘ i =
        (fun p : P ↦ g p) ∘ i := by
    funext f
    have hif : i f = ⟨f.1, S.le_topologicalClosure f.2⟩ := by
      apply Subtype.ext
      rfl
    change f.1 (vectorFunctionalClosureRecover g) = g (i f)
    rw [hif]
    refine Submodule.span_induction (p := fun h hh ↦ h (vectorFunctionalClosureRecover g) =
        g ⟨h, S.le_topologicalClosure hh⟩)
      ?_ ?_ ?_ ?_ f.2
    · intro h hh
      rw [mem_vectorFunctionals_iff] at hh
      obtain ⟨xi, eta, rfl⟩ := hh
      exact vectorFunctionalClosureRecover_vectorFunctional g xi eta
    · change (0 : 𝕜) = g (0 : P)
      simp
    · intro x y hx hy hxi hyi
      change (x + y) (vectorFunctionalClosureRecover g) =
        g ((⟨x, S.le_topologicalClosure hx⟩ : P) +
          (⟨y, S.le_topologicalClosure hy⟩ : P))
      simpa only [add_apply, map_add] using congrArg₂ (· + ·) hxi hyi
    · intro c x hx hxi
      change (c • x) (vectorFunctionalClosureRecover g) =
        g (c • (⟨x, S.le_topologicalClosure hx⟩ : P))
      simpa only [smul_apply, map_smul, RingHom.id_apply] using congrArg (c • ·) hxi
  have heq :
      (fun p : P ↦ vectorFunctionalClosureEvaluation
          (vectorFunctionalClosureRecover g) p) = fun p : P ↦ g p :=
    hi.equalizer
      (vectorFunctionalClosureEvaluation (vectorFunctionalClosureRecover g)).continuous
      g.continuous hcomp
  exact ContinuousLinearMap.ext fun p ↦ congrFun heq p

/-- Canonical evaluation onto the dual of the norm-closed vector-functional space is
surjective. -/
theorem vectorFunctionalClosureEvaluation_surjective :
    Function.Surjective
      (vectorFunctionalClosureEvaluation (𝕜 := 𝕜) (E := E) (F := F)) :=
  fun g ↦ ⟨vectorFunctionalClosureRecover g, vectorFunctionalClosureEvaluation_recover g⟩

omit [CompleteSpace F] in
/-- Canonical evaluation on the norm-closed vector-functional space is injective. -/
lemma vectorFunctionalClosureEvaluation_injective :
    Function.Injective
      (vectorFunctionalClosureEvaluation (𝕜 := 𝕜) (E := E) (F := F)) := by
  intro S T hST
  apply ext_vectorFunctional
  intro xi eta
  have h := congrArg
    (fun g : StrongDual 𝕜
      (vectorFunctionalClosure (𝕜 := 𝕜) (E := E) (F := F)) ↦
        g (vectorFunctionalInClosure xi eta)) hST
  simpa only [vectorFunctionalClosureEvaluation_apply_apply,
    coe_vectorFunctionalInClosure] using h

/-- A space of bounded maps into a Hilbert space is canonically the dual of the norm closure of
its vector functionals. -/
def vectorFunctionalClosureEquivDual :
    (E →L[𝕜] F) ≃ₗᵢ[𝕜]
      StrongDual 𝕜 (vectorFunctionalClosure (𝕜 := 𝕜) (E := E) (F := F)) where
  toFun := vectorFunctionalClosureEvaluation
  invFun := vectorFunctionalClosureRecover
  left_inv T := by
    apply vectorFunctionalClosureEvaluation_injective
    rw [vectorFunctionalClosureEvaluation_recover]
  right_inv := vectorFunctionalClosureEvaluation_recover
  map_add' := map_add vectorFunctionalClosureEvaluation
  map_smul' := map_smul vectorFunctionalClosureEvaluation
  norm_map' := norm_vectorFunctionalClosureEvaluation

@[simp]
lemma vectorFunctionalClosureEquivDual_apply_apply (T : E →L[𝕜] F)
    (f : vectorFunctionalClosure (𝕜 := 𝕜) (E := E) (F := F)) :
    vectorFunctionalClosureEquivDual T f = f.1 T :=
  rfl

end Complete

end ContinuousLinearMap
