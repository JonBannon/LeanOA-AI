module

public import LeanOA.Ultraweak.Corner
public import LeanOA.Ultraweak.Masa
public import Mathlib.Topology.UniformSpace.UniformApproximation

@[expose] public section

/-!
# Ultraweak continuity of multiplication

The principal intermediate object is the norm-closed submodule of elements whose left
multiplication map is ultraweakly continuous. This makes continuity under norm approximation a
reusable statement rather than repeating an argument on the closed unit ball.
-/

open Filter Set
open scoped Ultraweak

namespace Ultraweak

section Generic

variable {𝕜 M P : Type*} [RCLike 𝕜]
  [NonUnitalNormedRing M] [NormedSpace 𝕜 M]
  [IsScalarTower 𝕜 M M] [SMulCommClass 𝕜 M M]
  [NormedAddCommGroup P] [NormedSpace 𝕜 P] [CompleteSpace P] [Predual 𝕜 M P]

/-- Elements whose left multiplication map is continuous for the specified ultraweak topology. -/
noncomputable def continuousLeftMultipliers : NonUnitalSubalgebra 𝕜 M where
  carrier := {a | Continuous (mulLeftₗ (𝕜 := 𝕜) (P := P) a)}
  zero_mem' := by
    change Continuous (mulLeftₗ (𝕜 := 𝕜) (P := P) 0)
    rw [map_zero]
    exact continuous_const
  add_mem' {a} {b} ha hb := by
    change Continuous (mulLeftₗ (𝕜 := 𝕜) (P := P) a) at ha
    change Continuous (mulLeftₗ (𝕜 := 𝕜) (P := P) b) at hb
    change Continuous (mulLeftₗ (𝕜 := 𝕜) (P := P) (a + b))
    rw [map_add]
    exact ha.add hb
  smul_mem' c {a} ha := by
    change Continuous (mulLeftₗ (𝕜 := 𝕜) (P := P) a) at ha
    change Continuous (mulLeftₗ (𝕜 := 𝕜) (P := P) (c • a))
    rw [map_smul]
    exact ha.const_smul c
  mul_mem' {a b} ha hb := by
    change Continuous (mulLeftₗ (𝕜 := 𝕜) (P := P) a) at ha
    change Continuous (mulLeftₗ (𝕜 := 𝕜) (P := P) b) at hb
    change Continuous (mulLeftₗ (𝕜 := 𝕜) (P := P) (a * b))
    rw [mulLeftₗ_mul]
    exact ha.comp hb

omit [CompleteSpace P] in
@[simp]
lemma mem_continuousLeftMultipliers (a : M) :
    a ∈ continuousLeftMultipliers (𝕜 := 𝕜) (M := M) (P := P) ↔
      Continuous (mulLeftₗ (𝕜 := 𝕜) (P := P) a) :=
  Iff.rfl

/-- Ultraweakly continuous left multipliers are closed under norm limits. -/
theorem isClosed_continuousLeftMultipliers :
    IsClosed (continuousLeftMultipliers (𝕜 := 𝕜) (M := M) (P := P) : Set M) := by
  rw [← isSeqClosed_iff_isClosed]
  intro u a hu hua
  have hu' (n : ℕ) : Continuous (mulLeftₗ (𝕜 := 𝕜) (P := P) (u n)) :=
    (mem_continuousLeftMultipliers (P := P) (u n)).mp (hu n)
  change Continuous (mulLeftₗ (𝕜 := 𝕜) (P := P) a)
  apply continuous_of_continuousOn
  rw [continuousOn_iff_continuous_restrict]
  apply continuous_of_continuous_eval
  intro q
  let B : Set (σ(M, P)_𝕜) := ofUltraweak ⁻¹' Metric.closedBall (0 : M) 1
  let F : ℕ → B → 𝕜 := fun n x ↦
    Predual.equivDual (𝕜 := 𝕜) (u n * ofUltraweak x.1) q
  let f : B → 𝕜 := fun x ↦
    Predual.equivDual (𝕜 := 𝕜) (a * ofUltraweak x.1) q
  apply TendstoUniformly.continuous (F := F) (f := f) (p := atTop)
  · refine Metric.tendstoUniformly_iff.mpr ?_
    intro ε hε
    have hq : 0 < ‖q‖ + 1 := by positivity
    filter_upwards [hua.eventually (Metric.ball_mem_nhds a (div_pos hε hq))] with n hn x
    have hx : ‖ofUltraweak x.1‖ ≤ 1 := by
      have hx := x.2
      change ofUltraweak x.1 ∈ Metric.closedBall (0 : M) 1 at hx
      simpa [Metric.mem_closedBall, dist_zero_right] using hx
    calc
      dist (f x) (F n x) =
          ‖Predual.equivDual (𝕜 := 𝕜) ((a - u n) * ofUltraweak x.1) q‖ := by
        simp only [f, F, dist_eq_norm]
        congr 1
        rw [sub_mul, map_sub, sub_apply]
      _ ≤ ‖Predual.equivDual (𝕜 := 𝕜) ((a - u n) * ofUltraweak x.1)‖ * ‖q‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖(a - u n) * ofUltraweak x.1‖ * ‖q‖ := by
        rw [(Predual.equivDual (𝕜 := 𝕜) (M := M) (P := P)).norm_map]
      _ ≤ (‖a - u n‖ * ‖ofUltraweak x.1‖) * ‖q‖ := by
        gcongr
        exact norm_mul_le ..
      _ ≤ ‖a - u n‖ * 1 * ‖q‖ := by gcongr
      _ < ε / (‖q‖ + 1) * (‖q‖ + 1) := by
        rw [mul_one]
        gcongr
        · simpa [dist_eq_norm, norm_sub_rev] using hn
        · linarith [norm_nonneg q]
      _ = ε := by field_simp
  · exact Frequently.of_forall fun n ↦ by
      change Continuous fun x : B ↦ Predual.equivDual (𝕜 := 𝕜)
        (ofUltraweak (mulLeftₗ (𝕜 := 𝕜) (P := P) (u n) x.1)) q
      exact (Ultraweak.eval_continuous (𝕜 := 𝕜) (M := M) (P := P) q).comp <|
        (hu' n).comp continuous_subtype_val

end Generic

section CStarAlgebra

variable {M P : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]

include P in
/-- A projection is an ultraweakly continuous left multiplier. -/
theorem _root_.IsStarProjection.mem_continuousLeftMultipliers {p : M}
    (hp : IsStarProjection p) :
    p ∈ continuousLeftMultipliers (𝕜 := ℂ) (M := M) (P := P) :=
  (Ultraweak.mem_continuousLeftMultipliers (𝕜 := ℂ) (P := P) p).mpr <|
    IsStarProjection.continuous_ultraweakMulLeftₗ (M := M) (P := P) hp

include P in
/-- Left multiplication by a self-adjoint element is ultraweakly continuous. -/
theorem _root_.IsSelfAdjoint.continuous_ultraweakMulLeftₗ {a : M}
    (ha : IsSelfAdjoint a) :
    Continuous (mulLeftₗ (𝕜 := ℂ) (P := P) a) := by
  apply (Ultraweak.mem_continuousLeftMultipliers (𝕜 := ℂ) (P := P) a).mp
  have hspan : Submodule.span ℝ {p : M | IsStarProjection p} ≤
      (continuousLeftMultipliers (𝕜 := ℂ) (M := M) (P := P)).toSubmodule.restrictScalars ℝ :=
    Submodule.span_le.mpr fun _ hp ↦
      IsStarProjection.mem_continuousLeftMultipliers (P := P) hp
  apply closure_minimal hspan <|
    isClosed_continuousLeftMultipliers (𝕜 := ℂ) (M := M) (P := P)
  exact ha.mem_topologicalClosure_span_isStarProjection_of_predual (P := P)

/-- Left multiplication by any element is ultraweakly continuous. -/
theorem continuous_mulLeftₗ (a : M) :
    Continuous (mulLeftₗ (𝕜 := ℂ) (P := P) a) := by
  apply (Ultraweak.mem_continuousLeftMultipliers (𝕜 := ℂ) (P := P) a).mp
  rw [← realPart_add_I_smul_imaginaryPart a]
  exact (continuousLeftMultipliers (𝕜 := ℂ) (M := M) (P := P)).add_mem
    (IsSelfAdjoint.continuous_ultraweakMulLeftₗ (P := P) (realPart a).2)
    ((continuousLeftMultipliers (𝕜 := ℂ) (M := M) (P := P)).smul_mem Complex.I <|
      IsSelfAdjoint.continuous_ultraweakMulLeftₗ (P := P) (imaginaryPart a).2)

/-- Right multiplication by any element is ultraweakly continuous. -/
theorem continuous_mulRightₗ (a : M) :
    Continuous (mulRightₗ (𝕜 := ℂ) (P := P) a) := by
  rw [show (mulRightₗ (𝕜 := ℂ) (P := P) a : σ(M, P) → σ(M, P)) =
      fun x ↦ star (mulLeftₗ (𝕜 := ℂ) (P := P) (star a) (star x)) by
    funext x
    rw [← ofUltraweak_inj]
    simp [star_mul]]
  exact continuous_star.comp ((continuous_mulLeftₗ (P := P) (star a)).comp continuous_star)

/-- Multiplication in a C⋆-algebra is separately continuous for its specified ultraweak
topology. -/
instance : SeparatelyContinuousMul σ(M, P) where
  continuous_const_mul {a} := by
    change Continuous (mulLeftₗ (𝕜 := ℂ) (P := P) (ofUltraweak a))
    exact continuous_mulLeftₗ (P := P) (ofUltraweak a)
  continuous_mul_const {a} := by
    change Continuous (mulRightₗ (𝕜 := ℂ) (P := P) (ofUltraweak a))
    exact continuous_mulRightₗ (P := P) (ofUltraweak a)

/-- The ultraweak topology and its transported ring structure make a semitopological ring. -/
instance : IsSemitopologicalRing σ(M, P) := by
  letI : IsSemitopologicalSemiring σ(M, P) := IsSemitopologicalSemiring.mk
  exact IsSemitopologicalRing.mk

/-- Ultraweakly continuous left multiplication by a fixed element. -/
noncomputable def mulLeftL (a : M) : σ(M, P) →L[ℂ] σ(M, P) :=
  ⟨mulLeftₗ (𝕜 := ℂ) (P := P) a, continuous_mulLeftₗ (P := P) a⟩

@[simp]
lemma mulLeftL_apply (a : M) (x : σ(M, P)) :
    mulLeftL (P := P) a x = toUltraweak ℂ P (a * ofUltraweak x) := rfl

/-- The range of ultraweak left multiplication is the explicit transport of the corresponding
normed-space range. -/
lemma range_mulLeftL (a : M) :
    LinearMap.range (mulLeftL (P := P) a).toLinearMap =
      ofSubmodule (P := P) (LinearMap.range (LinearMap.mul ℂ M a)) := by
  ext x
  rw [LinearMap.mem_range, mem_ofSubmodule, LinearMap.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨ofUltraweak y, by simp⟩
  · rintro ⟨y, hy⟩
    refine ⟨toUltraweak ℂ P y, ?_⟩
    change mulLeftL (P := P) a (toUltraweak ℂ P y) = x
    rw [← ofUltraweak_inj]
    simpa only [mulLeftL_apply, ofUltraweak_toUltraweak, ContinuousLinearMap.coe_coe,
      LinearMap.mul_apply'] using hy

include P in
/-- Left multiplication by an idempotent is an idempotent continuous linear map on the
ultraweak space. -/
lemma _root_.IsIdempotentElem.mulLeftL {a : M} (ha : IsIdempotentElem a) :
    IsIdempotentElem (mulLeftL (P := P) a) := by
  rw [isIdempotentElem_iff]
  ext x
  rw [mul_apply_eq_comp]
  simp only [mulLeftL_apply, ofUltraweak_toUltraweak]
  rw [← mul_assoc, ha.eq]

/-- Ultraweakly continuous right multiplication by a fixed element. -/
noncomputable def mulRightL (a : M) : σ(M, P) →L[ℂ] σ(M, P) :=
  ⟨mulRightₗ (𝕜 := ℂ) (P := P) a, continuous_mulRightₗ (P := P) a⟩

@[simp]
lemma mulRightL_apply (a : M) (x : σ(M, P)) :
    mulRightL (P := P) a x = toUltraweak ℂ P (ofUltraweak x * a) := rfl

/-- The range of ultraweak right multiplication is the explicit transport of the corresponding
normed-space range. -/
lemma range_mulRightL (a : M) :
    LinearMap.range (mulRightL (P := P) a).toLinearMap =
      ofSubmodule (P := P) (LinearMap.range (LinearMap.mulRight ℂ a)) := by
  ext x
  rw [LinearMap.mem_range, mem_ofSubmodule, LinearMap.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨ofUltraweak y, by simp⟩
  · rintro ⟨y, hy⟩
    refine ⟨toUltraweak ℂ P y, ?_⟩
    change mulRightL (P := P) a (toUltraweak ℂ P y) = x
    rw [← ofUltraweak_inj]
    simpa only [mulRightL_apply, ofUltraweak_toUltraweak, LinearMap.mulRight_apply] using hy

include P in
/-- Right multiplication by an idempotent is an idempotent continuous linear map on the
ultraweak space. -/
lemma _root_.IsIdempotentElem.mulRightL {a : M} (ha : IsIdempotentElem a) :
    IsIdempotentElem (mulRightL (P := P) a) := by
  rw [isIdempotentElem_iff]
  ext x
  rw [mul_apply_eq_comp]
  simp only [mulRightL_apply, ofUltraweak_toUltraweak]
  rw [mul_assoc, ha.eq]

end CStarAlgebra

end Ultraweak
