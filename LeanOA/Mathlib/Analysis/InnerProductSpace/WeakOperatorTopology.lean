module

public import LeanOA.Mathlib.Topology.Algebra.Module.WeakBilin
public import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Topology.Algebra.Star.LinearMap
public import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM

/-!
# Vector functionals on continuous linear maps

This file packages the vector functional

`T ↦ ⟪η, T ξ⟫_𝕜`

on a space of continuous linear maps.  The order of the inner-product arguments makes this
functional linear under Mathlib's convention.  The file also provides its adjoint, composition,
separation, linear-span, and intrinsic-star APIs.

It also identifies the weak topology induced by the vector-functional span with Mathlib's weak
operator topology. No new topology-bearing type is introduced.

Finally, it gives the filter-general positive-square criterion relating pointwise (strong
operator) convergence to weak-operator convergence.
-/

@[expose] public section

open scoped InnerProduct InnerProductSpace

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The vector functional `T ↦ ⟪η, T ξ⟫_𝕜` on continuous linear maps. -/
noncomputable def vectorFunctional (ξ : E) (η : F) : (E →L[𝕜] F) →L[𝕜] 𝕜 :=
  (innerSL 𝕜 η).comp (ContinuousLinearMap.apply 𝕜 F ξ)

@[simp]
lemma vectorFunctional_apply (ξ : E) (η : F) (T : E →L[𝕜] F) :
    vectorFunctional ξ η T = ⟪η, T ξ⟫_𝕜 := rfl

section Adjoint

variable {E₁ F₁ : Type*}
  [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [CompleteSpace E₁]
  [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁] [CompleteSpace F₁]

/-- Taking the adjoint of an operator exchanges the vectors in its vector functional and
conjugates the value. -/
lemma vectorFunctional_adjoint_apply (ξ : E₁) (η : F₁) (T : E₁ →L[𝕜] F₁) :
    vectorFunctional η ξ (T†) = star (vectorFunctional ξ η T) := by
  rw [vectorFunctional_apply, adjoint_inner_right, vectorFunctional_apply]
  exact (inner_conj_symm (𝕜 := 𝕜) (T ξ) η).symm

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- The endomorphism-star specialization of `vectorFunctional_adjoint_apply`. -/
lemma vectorFunctional_star_apply (ξ η : H) (T : H →L[𝕜] H) :
    vectorFunctional ξ η (star T) = star (vectorFunctional η ξ T) := by
  simpa only [star_eq_adjoint] using vectorFunctional_adjoint_apply η ξ T

end Adjoint

section Composition

variable {G : Type*} [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

variable [CompleteSpace F] in
/-- Precomposing an operator-valued argument by fixed left composition moves the adjoint of the
fixed operator to the second vector. -/
lemma vectorFunctional_comp_left (ξ : E) (η : F) (a : F →L[𝕜] F) (T : E →L[𝕜] F) :
    vectorFunctional ξ η (a.comp T) = vectorFunctional ξ ((a†) η) T := by
  rw [vectorFunctional_apply, comp_apply, vectorFunctional_apply, adjoint_inner_left]

/-- Fixed right composition moves the fixed operator to the first vector. -/
@[simp]
lemma vectorFunctional_comp_right (ξ : G) (η : F) (T : E →L[𝕜] F) (a : G →L[𝕜] E) :
    vectorFunctional ξ η (T.comp a) = vectorFunctional (a ξ) η T := rfl

end Composition

section Endomorphism

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

variable [CompleteSpace H] in
/-- The vector-functional formula for multiplication on the left by a fixed operator. -/
lemma vectorFunctional_mul_left (ξ η : H) (a T : H →L[𝕜] H) :
    vectorFunctional ξ η (a * T) = vectorFunctional ξ (star a η) T := by
  change vectorFunctional ξ η (a.comp T) = _
  simpa only [star_eq_adjoint] using vectorFunctional_comp_left ξ η a T

/-- The vector-functional formula for multiplication on the right by a fixed operator. -/
lemma vectorFunctional_mul_right (ξ η : H) (T a : H →L[𝕜] H) :
    vectorFunctional ξ η (T * a) = vectorFunctional (a ξ) η T := by
  change vectorFunctional ξ η (T.comp a) = _
  exact vectorFunctional_comp_right ξ η T a

end Endomorphism

/-- Vector functionals separate continuous linear maps. -/
theorem ext_vectorFunctional {S T : E →L[𝕜] F}
    (h : ∀ ξ η, vectorFunctional ξ η S = vectorFunctional ξ η T) : S = T := by
  ext ξ
  exact ext_inner_left 𝕜 fun η ↦ h ξ η

/-- A continuous linear map annihilated by every vector functional is zero.  This includes the
zero Hilbert space and needs no nontriviality assumption. -/
theorem eq_zero_of_forall_vectorFunctional_eq_zero {T : E →L[𝕜] F}
    (h : ∀ ξ η, vectorFunctional ξ η T = 0) : T = 0 := by
  apply ContinuousLinearMap.ext
  intro ξ
  exact inner_self_eq_zero.mp (h ξ (T ξ))

/-- The raw set of vector functionals on a space of continuous linear maps. -/
def vectorFunctionals : Set ((E →L[𝕜] F) →L[𝕜] 𝕜) :=
  Set.range fun p : E × F ↦ vectorFunctional p.1 p.2

lemma vectorFunctional_mem_vectorFunctionals (ξ : E) (η : F) :
    vectorFunctional ξ η ∈ vectorFunctionals (𝕜 := 𝕜) (E := E) (F := F) :=
  ⟨(ξ, η), rfl⟩

lemma mem_vectorFunctionals_iff {f : (E →L[𝕜] F) →L[𝕜] 𝕜} :
    f ∈ vectorFunctionals (𝕜 := 𝕜) (E := E) (F := F) ↔
      ∃ ξ η, vectorFunctional ξ η = f := by
  constructor
  · rintro ⟨⟨ξ, η⟩, rfl⟩
    exact ⟨ξ, η, rfl⟩
  · rintro ⟨ξ, η, rfl⟩
    exact vectorFunctional_mem_vectorFunctionals ξ η

/-- The algebraic span of all vector functionals on a space of continuous linear maps. -/
def vectorFunctionalSpan : Submodule 𝕜 ((E →L[𝕜] F) →L[𝕜] 𝕜) :=
  Submodule.span 𝕜 (vectorFunctionals (𝕜 := 𝕜) (E := E) (F := F))

lemma vectorFunctional_mem_span (ξ : E) (η : F) :
    vectorFunctional ξ η ∈ vectorFunctionalSpan (𝕜 := 𝕜) (E := E) (F := F) :=
  Submodule.subset_span (vectorFunctional_mem_vectorFunctionals ξ η)

/-- The span of the vector functionals separates continuous linear maps. -/
theorem ext_vectorFunctionalSpan {S T : E →L[𝕜] F}
    (h : ∀ f, f ∈ vectorFunctionalSpan (𝕜 := 𝕜) (E := E) (F := F) → f S = f T) :
    S = T :=
  ext_vectorFunctional fun ξ η ↦ h _ (vectorFunctional_mem_span ξ η)

/-- A continuous linear map annihilated by the span of the vector functionals is zero. -/
theorem eq_zero_of_forall_mem_vectorFunctionalSpan_eq_zero {T : E →L[𝕜] F}
    (h : ∀ f, f ∈ vectorFunctionalSpan (𝕜 := 𝕜) (E := E) (F := F) → f T = 0) :
    T = 0 :=
  eq_zero_of_forall_vectorFunctional_eq_zero fun ξ η ↦
    h _ (vectorFunctional_mem_span ξ η)

section EndomorphismSpanRight

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- Precomposing a vector functional by fixed right multiplication produces another vector
functional. -/
@[simp]
theorem vectorFunctional_comp_mulRight (ξ η : H) (a : H →L[𝕜] H) :
    (vectorFunctional (𝕜 := 𝕜) ξ η).comp
        (ContinuousLinearMap.mulLeftRight 𝕜 (H →L[𝕜] H) 1 a) =
      vectorFunctional (𝕜 := 𝕜) (a ξ) η := by
  ext T
  rw [comp_apply, mulLeftRight_apply, one_mul, vectorFunctional_mul_right]

/-- The vector-functional span is stable under precomposition by fixed right multiplication. -/
theorem comp_mulRight_mem_vectorFunctionalSpan (a : H →L[𝕜] H)
    {f : (H →L[𝕜] H) →L[𝕜] 𝕜}
    (hf : f ∈ vectorFunctionalSpan (𝕜 := 𝕜) (E := H) (F := H)) :
    f.comp (ContinuousLinearMap.mulLeftRight 𝕜 (H →L[𝕜] H) 1 a) ∈
      vectorFunctionalSpan (𝕜 := 𝕜) (E := H) (F := H) := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
  · intro g hg
    rw [mem_vectorFunctionals_iff] at hg
    obtain ⟨ξ, η, rfl⟩ := hg
    rw [vectorFunctional_comp_mulRight]
    exact vectorFunctional_mem_span _ _
  · simp
  · intro g h hg hh ihg ihh
    simpa using (vectorFunctionalSpan (𝕜 := 𝕜) (E := H) (F := H)).add_mem ihg ihh
  · intro c g hg ih
    simpa using (vectorFunctionalSpan (𝕜 := 𝕜) (E := H) (F := H)).smul_mem c ih

end EndomorphismSpanRight

section EndomorphismSpan

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- Mathlib's intrinsic involution on the norm dual exchanges the vectors in a vector
functional. -/
@[simp]
theorem intrinsicStar_vectorFunctional (ξ η : H) :
    (star (WithConv.toConv (vectorFunctional (𝕜 := 𝕜) ξ η))).ofConv =
      vectorFunctional (𝕜 := 𝕜) η ξ := by
  ext T
  simp only [intrinsicStar_apply, vectorFunctional_star_apply, star_star]

/-- The vector-functional span is stable under Mathlib's intrinsic involution on the norm dual. -/
theorem intrinsicStar_mem_vectorFunctionalSpan
    {f : (H →L[𝕜] H) →L[𝕜] 𝕜}
    (hf : f ∈ vectorFunctionalSpan (𝕜 := 𝕜) (E := H) (F := H)) :
    (star (WithConv.toConv f)).ofConv ∈
      vectorFunctionalSpan (𝕜 := 𝕜) (E := H) (F := H) := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
  · intro g hg
    rw [mem_vectorFunctionals_iff] at hg
    obtain ⟨ξ, η, rfl⟩ := hg
    rw [intrinsicStar_vectorFunctional]
    exact vectorFunctional_mem_span _ _
  · simpa only [intrinsicStar_zero] using
      (vectorFunctionalSpan (𝕜 := 𝕜) (E := H) (F := H)).zero_mem
  · intro g h hg hh ihg ihh
    have hmap :
        (star (WithConv.toConv (g + h))).ofConv =
          (star (WithConv.toConv g)).ofConv + (star (WithConv.toConv h)).ofConv := by
      ext T
      simp only [intrinsicStar_apply, add_apply, star_add]
    rw [hmap]
    exact (vectorFunctionalSpan (𝕜 := 𝕜) (E := H) (F := H)).add_mem ihg ihh
  · intro c g hg ih
    have hmap :
        (star (WithConv.toConv (c • g))).ofConv =
          star c • (star (WithConv.toConv g)).ofConv := by
      ext T
      simp only [intrinsicStar_apply, smul_apply, star_smul]
    rw [hmap]
    exact (vectorFunctionalSpan (𝕜 := 𝕜) (E := H) (F := H)).smul_mem (star c) ih

/-- Precomposing a vector functional by two-sided multiplication produces another vector
functional. -/
@[simp]
theorem vectorFunctional_comp_mulLeftRight (ξ η : H) (a b : H →L[𝕜] H) :
    (vectorFunctional (𝕜 := 𝕜) ξ η).comp
        (ContinuousLinearMap.mulLeftRight 𝕜 (H →L[𝕜] H) a b) =
      vectorFunctional (𝕜 := 𝕜) (b ξ) (star a η) := by
  ext T
  rw [comp_apply, mulLeftRight_apply,
    vectorFunctional_mul_right ξ η (a * T) b,
    vectorFunctional_mul_left (b ξ) η a T]

/-- The vector-functional span is stable under precomposition by fixed two-sided
multiplication. -/
theorem comp_mulLeftRight_mem_vectorFunctionalSpan (a b : H →L[𝕜] H)
    {f : (H →L[𝕜] H) →L[𝕜] 𝕜}
    (hf : f ∈ vectorFunctionalSpan (𝕜 := 𝕜) (E := H) (F := H)) :
    f.comp (ContinuousLinearMap.mulLeftRight 𝕜 (H →L[𝕜] H) a b) ∈
      vectorFunctionalSpan (𝕜 := 𝕜) (E := H) (F := H) := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
  · intro g hg
    rw [mem_vectorFunctionals_iff] at hg
    obtain ⟨ξ, η, rfl⟩ := hg
    rw [vectorFunctional_comp_mulLeftRight]
    exact vectorFunctional_mem_span _ _
  · simp
  · intro g h hg hh ihg ihh
    simpa using (vectorFunctionalSpan (𝕜 := 𝕜) (E := H) (F := H)).add_mem ihg ihh
  · intro c g hg ih
    simpa using (vectorFunctionalSpan (𝕜 := 𝕜) (E := H) (F := H)).smul_mem c ih

/-- The vector-functional span is stable under precomposition by fixed left multiplication. -/
theorem comp_mulLeft_mem_vectorFunctionalSpan (a : H →L[𝕜] H)
    {f : (H →L[𝕜] H) →L[𝕜] 𝕜}
    (hf : f ∈ vectorFunctionalSpan (𝕜 := 𝕜) (E := H) (F := H)) :
    f.comp (ContinuousLinearMap.mulLeftRight 𝕜 (H →L[𝕜] H) a 1) ∈
      vectorFunctionalSpan (𝕜 := 𝕜) (E := H) (F := H) :=
  comp_mulLeftRight_mem_vectorFunctionalSpan a 1 hf

end EndomorphismSpan

/-- Evaluation of continuous linear maps against the span of their vector functionals. -/
noncomputable def vectorFunctionalPairing :
    (E →L[𝕜] F) →ₗ[𝕜]
      vectorFunctionalSpan (𝕜 := 𝕜) (E := E) (F := F) →ₗ[𝕜] 𝕜 :=
  ((ContinuousLinearMap.coeLM 𝕜).comp
    (vectorFunctionalSpan (𝕜 := 𝕜) (E := E) (F := F)).subtype).flip

@[simp]
lemma vectorFunctionalPairing_apply (T : E →L[𝕜] F)
    (f : vectorFunctionalSpan (𝕜 := 𝕜) (E := E) (F := F)) :
    vectorFunctionalPairing T f = f.1 T :=
  rfl

end ContinuousLinearMap

namespace ContinuousLinearMapWOT

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

private lemma continuous_vectorFunctionalSpan_apply
    (f : ContinuousLinearMap.vectorFunctionalSpan (𝕜 := 𝕜) (E := E) (F := F)) :
    Continuous fun T : E →WOT[𝕜] F ↦ f.1 T.toCLM := by
  refine Submodule.span_induction
    (s := ContinuousLinearMap.vectorFunctionals (𝕜 := 𝕜) (E := E) (F := F))
    (p := fun g _ ↦ Continuous fun T : E →WOT[𝕜] F ↦ g T.toCLM)
    ?_ ?_ ?_ ?_ f.2
  · intro g hg
    rw [ContinuousLinearMap.mem_vectorFunctionals_iff] at hg
    obtain ⟨ξ, η, rfl⟩ := hg
    simpa only [ContinuousLinearMap.vectorFunctional_apply, toCLM_apply, id_eq] using
      (continuous_inner_apply continuous_id ξ η)
  · simpa using (continuous_const : Continuous fun _ : E →WOT[𝕜] F ↦ (0 : 𝕜))
  · intro g h _ _ hg hh
    change Continuous ((fun T : E →WOT[𝕜] F ↦ g T.toCLM) + fun T ↦ h T.toCLM)
    exact hg.add hh
  · intro c g _ hg
    change Continuous (c • fun T : E →WOT[𝕜] F ↦ g T.toCLM)
    exact hg.const_smul c

/-- The canonical continuous identity from the weak topology induced by the vector-functional
span to Mathlib's weak operator topology. -/
noncomputable def fromVectorFunctionalWeak :
    WeakBilin (ContinuousLinearMap.vectorFunctionalPairing
      (𝕜 := 𝕜) (E := E) (F := F)) →L[𝕜] (E →WOT[𝕜] F) where
  toFun T := ofCLM T
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous fun ξ η ↦ by
    let f : ContinuousLinearMap.vectorFunctionalSpan
        (𝕜 := 𝕜) (E := E) (F := F) :=
      ⟨ContinuousLinearMap.vectorFunctional ξ η,
        ContinuousLinearMap.vectorFunctional_mem_span ξ η⟩
    simpa [f] using WeakBilin.eval_continuous
      (ContinuousLinearMap.vectorFunctionalPairing
        (𝕜 := 𝕜) (E := E) (F := F)) f

@[simp]
lemma fromVectorFunctionalWeak_apply
    (T : WeakBilin (ContinuousLinearMap.vectorFunctionalPairing
      (𝕜 := 𝕜) (E := E) (F := F))) :
    fromVectorFunctionalWeak T = ofCLM T :=
  rfl

/-- The canonical continuous identity from Mathlib's weak operator topology to the weak topology
induced by the vector-functional span. -/
noncomputable def toVectorFunctionalWeak :
    (E →WOT[𝕜] F) →L[𝕜]
      WeakBilin (ContinuousLinearMap.vectorFunctionalPairing
        (𝕜 := 𝕜) (E := E) (F := F)) where
  toFun T := T.toCLM
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := WeakBilin.continuous_of_continuous_eval
    (ContinuousLinearMap.vectorFunctionalPairing
      (𝕜 := 𝕜) (E := E) (F := F)) fun f ↦ by
      simpa only [ContinuousLinearMap.vectorFunctionalPairing_apply] using
        continuous_vectorFunctionalSpan_apply f

@[simp]
lemma toVectorFunctionalWeak_apply (T : E →WOT[𝕜] F) :
    toVectorFunctionalWeak T = T.toCLM :=
  rfl

/-- The weak topology induced by the span of the vector functionals is canonically Mathlib's weak
operator topology. This is the raw-coefficient-versus-linear-span identification in both
directions. -/
noncomputable def vectorFunctionalWeakEquiv :
    WeakBilin (ContinuousLinearMap.vectorFunctionalPairing
      (𝕜 := 𝕜) (E := E) (F := F)) ≃L[𝕜] (E →WOT[𝕜] F) where
  toLinearEquiv :=
    { toFun := fromVectorFunctionalWeak
      invFun := toVectorFunctionalWeak
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := map_add fromVectorFunctionalWeak
      map_smul' := map_smul fromVectorFunctionalWeak }
  continuous_toFun := fromVectorFunctionalWeak.continuous
  continuous_invFun := toVectorFunctionalWeak.continuous

@[simp]
lemma vectorFunctionalWeakEquiv_apply
    (T : WeakBilin (ContinuousLinearMap.vectorFunctionalPairing
      (𝕜 := 𝕜) (E := E) (F := F))) :
    vectorFunctionalWeakEquiv T = ofCLM T :=
  rfl

@[simp]
lemma vectorFunctionalWeakEquiv_symm_apply (T : E →WOT[𝕜] F) :
    (vectorFunctionalWeakEquiv (𝕜 := 𝕜) (E := E) (F := F)).symm T = T.toCLM :=
  rfl

end ContinuousLinearMapWOT

namespace ContinuousLinearMap

section PositiveSquare

variable {𝕜 E F I : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- A matrix coefficient of `D† ∘L D` is the corresponding inner product of images under `D`. -/
lemma inner_adjoint_comp_self (D : E →L[𝕜] F) (x y : E) :
    ⟪y, ((D†).comp D) x⟫_𝕜 = ⟪D y, D x⟫_𝕜 := by
  rw [comp_apply, adjoint_inner_right]

/-- If two operators have respective norm bounds `rT` and `rA`, then their positive-square
difference has norm at most `(rT + rA) ^ 2`. No separate nonnegativity assumptions on the
bounds are needed. -/
theorem norm_adjoint_comp_sub_self_le_add_sq {rT rA : ℝ} {T A : E →L[𝕜] F}
    (hT : ‖T‖ ≤ rT) (hA : ‖A‖ ≤ rA) :
    ‖((T - A)†).comp (T - A)‖ ≤ (rT + rA) ^ 2 := by
  rw [norm_adjoint_comp_self]
  have hrT : 0 ≤ rT := (norm_nonneg T).trans hT
  have hrA : 0 ≤ rA := (norm_nonneg A).trans hA
  have hD : ‖T - A‖ ≤ rT + rA := by
    calc
      ‖T - A‖ ≤ ‖T‖ + ‖A‖ := norm_sub_le T A
      _ ≤ rT + rA := add_le_add hT hA
  calc
    ‖T - A‖ * ‖T - A‖ ≤ (rT + rA) * (rT + rA) :=
      mul_le_mul hD hD (norm_nonneg _) (by positivity)
    _ = (rT + rA) ^ 2 := by ring

/-- The eventual version of `norm_adjoint_comp_sub_self_le_add_sq`, used to place a
positive-square error family in one fixed norm ball. -/
theorem eventually_norm_adjoint_comp_sub_self_le_add_sq
    {l : Filter I} {rT rA : ℝ} {T : I → E →L[𝕜] F} {A : E →L[𝕜] F}
    (hT : ∀ᶠ i in l, ‖T i‖ ≤ rT) (hA : ‖A‖ ≤ rA) :
    ∀ᶠ i in l, ‖((T i - A)†).comp (T i - A)‖ ≤ (rT + rA) ^ 2 :=
  hT.mono fun _ hi ↦ norm_adjoint_comp_sub_self_le_add_sq hi hA

end PositiveSquare

end ContinuousLinearMap

namespace ContinuousLinearMapWOT

section PositiveSquare

variable {𝕜 E F I : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Pointwise convergence of operators is equivalent to weak-operator convergence to zero of
their positive-square errors. This holds for arbitrary filters and requires no uniform operator
norm bound. -/
theorem tendsto_pointwise_iff_tendsto_wot_adjoint_comp_self
    {l : Filter I} {T : I → E →L[𝕜] F} {A : E →L[𝕜] F} :
    (∀ x, Filter.Tendsto (fun i ↦ T i x) l (nhds (A x))) ↔
      Filter.Tendsto
        (fun i ↦ ContinuousLinearMapWOT.ofCLM
          (((T i - A)†).comp (T i - A)))
        l (nhds 0) := by
  constructor
  · intro h
    rw [tendsto_iff_forall_inner_apply_tendsto]
    intro x y
    have hx : Filter.Tendsto (fun i ↦ (T i - A) x) l (nhds 0) := by
      change Filter.Tendsto (fun i ↦ T i x - A x) l (nhds 0)
      simpa only [sub_self] using (h x).sub_const (A x)
    have hy : Filter.Tendsto (fun i ↦ (T i - A) y) l (nhds 0) := by
      change Filter.Tendsto (fun i ↦ T i y - A y) l (nhds 0)
      simpa only [sub_self] using (h y).sub_const (A y)
    have hinner : Filter.Tendsto
        (fun i ↦ ⟪(T i - A) y, (T i - A) x⟫_𝕜) l (nhds ⟪(0 : F), 0⟫_𝕜) :=
      hy.inner hx
    convert hinner using 1
    · funext i
      exact ContinuousLinearMap.inner_adjoint_comp_self (T i - A) x y
    · simp
  · intro h x
    rw [tendsto_iff_forall_inner_apply_tendsto] at h
    have hdiag : Filter.Tendsto
        (fun i ↦ ⟪x, (((T i - A)†).comp (T i - A)) x⟫_𝕜)
        l (nhds 0) := by
      simpa only [coe_ofCLM, zero_apply, inner_zero_right] using h x x
    have hre : Filter.Tendsto
        (fun i ↦ RCLike.re ⟪x, (((T i - A)†).comp (T i - A)) x⟫_𝕜)
        l (nhds 0) := by
      change Filter.Tendsto
        (RCLike.re ∘ fun i ↦ ⟪x, (((T i - A)†).comp (T i - A)) x⟫_𝕜)
        l (nhds 0)
      simpa only [map_zero] using
        RCLike.continuous_re.continuousAt.tendsto.comp hdiag
    have hsqrt : Filter.Tendsto
        (fun i ↦ Real.sqrt (RCLike.re
          ⟪x, (((T i - A)†).comp (T i - A)) x⟫_𝕜))
        l (nhds 0) := by
      change Filter.Tendsto
        (Real.sqrt ∘ fun i ↦ RCLike.re
          ⟪x, (((T i - A)†).comp (T i - A)) x⟫_𝕜)
        l (nhds 0)
      simpa only [Real.sqrt_zero] using
        Real.continuous_sqrt.continuousAt.tendsto.comp hre
    have hnorm : Filter.Tendsto (fun i ↦ ‖(T i - A) x‖) l (nhds 0) := by
      simpa only [ContinuousLinearMap.apply_norm_eq_sqrt_inner_adjoint_right,
        Function.comp_def] using hsqrt
    have hzero : Filter.Tendsto (fun i ↦ (T i - A) x) l (nhds 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
    exact tendsto_sub_nhds_zero_iff.mp hzero

section Endomorphism

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- The endomorphism-star form of
`ContinuousLinearMapWOT.tendsto_pointwise_iff_tendsto_wot_adjoint_comp_self`. -/
theorem tendsto_pointwise_iff_tendsto_wot_star_mul_self
    {l : Filter I} {T : I → H →L[𝕜] H} {A : H →L[𝕜] H} :
    (∀ x, Filter.Tendsto (fun i ↦ T i x) l (nhds (A x))) ↔
      Filter.Tendsto
        (fun i ↦ ContinuousLinearMapWOT.ofCLM
          (star (T i - A) * (T i - A)))
        l (nhds 0) := by
  simpa only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def] using
    (tendsto_pointwise_iff_tendsto_wot_adjoint_comp_self
      (l := l) (T := T) (A := A))

end Endomorphism

end PositiveSquare

end ContinuousLinearMapWOT

namespace PointwiseConvergenceCLM

section PositiveSquare

variable {𝕜 E F I : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Strong-operator convergence is equivalent to weak-operator convergence to zero of the
positive-square errors. The source and target Hilbert spaces may differ, and the statement is
filter-general. -/
theorem tendsto_iff_wot_adjoint_comp_self
    {l : Filter I} {T : I → E →Lₚₜ[𝕜] F} {A : E →Lₚₜ[𝕜] F} :
    Filter.Tendsto T l (nhds A) ↔
      Filter.Tendsto
        (fun i ↦ ContinuousLinearMapWOT.ofCLM
          (((((T i : E →L[𝕜] F) - (A : E →L[𝕜] F))†).comp
            ((T i : E →L[𝕜] F) - (A : E →L[𝕜] F)))))
        l (nhds 0) := by
  rw [PointwiseConvergenceCLM.tendsto_iff_forall_tendsto]
  exact ContinuousLinearMapWOT.tendsto_pointwise_iff_tendsto_wot_adjoint_comp_self
    (T := fun i ↦ (T i : E →L[𝕜] F)) (A := (A : E →L[𝕜] F))

section Endomorphism

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- The endomorphism-star form of `PointwiseConvergenceCLM.tendsto_iff_wot_adjoint_comp_self`. -/
theorem tendsto_iff_wot_star_mul_self
    {l : Filter I} {T : I → H →Lₚₜ[𝕜] H} {A : H →Lₚₜ[𝕜] H} :
    Filter.Tendsto T l (nhds A) ↔
      Filter.Tendsto
        (fun i ↦
          let D : H →L[𝕜] H := (T i : H →L[𝕜] H) - (A : H →L[𝕜] H)
          ContinuousLinearMapWOT.ofCLM (star D * D))
        l (nhds 0) := by
  rw [PointwiseConvergenceCLM.tendsto_iff_forall_tendsto]
  exact ContinuousLinearMapWOT.tendsto_pointwise_iff_tendsto_wot_star_mul_self
    (T := fun i ↦ (T i : H →L[𝕜] H)) (A := (A : H →L[𝕜] H))

end Endomorphism

end PositiveSquare

end PointwiseConvergenceCLM
