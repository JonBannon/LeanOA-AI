module

public import LeanOA.Mathlib.Analysis.CStarAlgebra.ApproximateUnit
public import LeanOA.Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import LeanOA.Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
public import LeanOA.PositiveContinuousLinearMap
public import LeanOA.Ultraweak.SeparatingDual
public import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal

import LeanOA.CFC

@[expose] public section

open scoped ComplexOrder

namespace PositiveLinearMap
section CauchySchwarz

open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion

-- we need to generalize GNS to this setting in order to get the Cauchy-Schwarz inequality
-- for positive linear functionals on type synonyms of C⋆-algebras.
variable {A : Type*} [NonUnitalRing A] [PartialOrder A] [Module ℂ A] (f : A →ₚ[ℂ] ℂ)

set_option linter.unusedVariables false in
/-- The Gelfand–Naimark–Segal (GNS) space constructed from a positive linear functional on a
non-unital C⋆-algebra. This is a type synonym of `A`.

This space is only a pre-inner product space. Its Hilbert space completion is
`Completion f.PreGNS'`. -/
@[nolint unusedArguments]
def PreGNS' (f : A →ₚ[ℂ] ℂ) := A

instance : AddCommGroup f.PreGNS' := inferInstanceAs (AddCommGroup A)
instance : Module ℂ f.PreGNS' := inferInstanceAs (Module ℂ A)

/-- The map from the C⋆-algebra to the GNS space, as a linear equivalence. -/
def toPreGNS' : A ≃ₗ[ℂ] f.PreGNS' := LinearEquiv.refl ℂ _

/-- The map from the GNS space to the C⋆-algebra, as a linear equivalence. -/
def ofPreGNS' : f.PreGNS' ≃ₗ[ℂ] A := f.toPreGNS'.symm

@[simp]
lemma toPreGNS'_ofPreGNS' (a : f.PreGNS') : f.toPreGNS' (f.ofPreGNS' a) = a := rfl

@[simp]
lemma ofPreGNS'_toPreGNS' (a : A) : f.ofPreGNS' (f.toPreGNS' a) = a := rfl

variable [StarRing A] [StarOrderedRing A] [SelfAdjointDecompose A] [StarModule ℂ A]
    [IsScalarTower ℂ A A]

/--
The (semi-)inner product space whose elements are the elements of `A`, but which has an
inner product-induced norm that is different from the norm on `A` and which is induced by `f`.
-/
noncomputable abbrev preGNS'preInnerProdSpace : PreInnerProductSpace.Core ℂ f.PreGNS' where
  inner a b := f (star (f.ofPreGNS' a) * f.ofPreGNS' b)
  conj_inner_symm := by simp [← Complex.star_def, ← map_star f]
  re_inner_nonneg _ := RCLike.nonneg_iff.mp (f.map_nonneg (star_mul_self_nonneg _)) |>.1
  add_left _ _ _ := by rw [map_add, star_add, add_mul, map_add]
  smul_left := by simp [smul_mul_assoc]

noncomputable instance : SeminormedAddCommGroup f.PreGNS' :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (c := f.preGNS'preInnerProdSpace)
noncomputable instance : InnerProductSpace ℂ f.PreGNS' :=
  InnerProductSpace.ofCore f.preGNS'preInnerProdSpace

lemma preGNS'_inner_def (a b : f.PreGNS') :
    ⟪a, b⟫_ℂ = f (star (f.ofPreGNS' a) * f.ofPreGNS' b) := rfl

lemma preGNS'_norm_def (a : f.PreGNS') :
    ‖a‖ = √(f (star (f.ofPreGNS' a) * f.ofPreGNS' a)).re := rfl

lemma preGNS'_norm_sq (a : f.PreGNS') :
    ‖a‖ ^ 2 = f (star (f.ofPreGNS' a) * f.ofPreGNS' a) := by
  have : 0 ≤ f (star (f.ofPreGNS' a) * f.ofPreGNS' a) := map_nonneg f <| star_mul_self_nonneg _
  rw [preGNS'_norm_def, ← ofReal_pow, Real.sq_sqrt]
  · rw [conj_eq_iff_re.mp this.star_eq]
  · rwa [re_nonneg_iff_nonneg this.isSelfAdjoint]

lemma preGNS'_norm_def' (f : A →ₚ[ℂ] ℂ) (a : f.PreGNS') :
    ‖a‖ = √‖f (star (f.ofPreGNS' a) * f.ofPreGNS' a)‖ := by
  rw [← sq_eq_sq₀ (by positivity) (by positivity), ← Complex.ofReal_inj,
    Complex.ofReal_pow, preGNS'_norm_sq, Real.sq_sqrt (by positivity),
    ← Complex.eq_coe_norm_of_nonneg]
  exact map_nonneg f (star_mul_self_nonneg _)

/-- The seminorm on a star algebra induced by a positive linear functional through its
Gelfand–Naimark–Segal construction. -/
noncomputable def gnsSeminorm (f : A →ₚ[ℂ] ℂ) : Seminorm ℂ A :=
  (normSeminorm ℂ f.PreGNS').comp f.toPreGNS'.toLinearMap

@[simp]
lemma gnsSeminorm_apply (f : A →ₚ[ℂ] ℂ) (x : A) :
    f.gnsSeminorm x = √‖f (star x * x)‖ := by
  simp [gnsSeminorm, preGNS'_norm_def']

lemma gnsSeminorm_mono (f g : A →ₚ[ℂ] ℂ)
    (h : ∀ x, 0 ≤ x → f x ≤ g x) : f.gnsSeminorm ≤ g.gnsSeminorm := fun x ↦ by
  rw [gnsSeminorm_apply, gnsSeminorm_apply]
  gcongr
  exact CStarAlgebra.norm_le_norm_of_nonneg_of_le
    (f.map_nonneg (star_mul_self_nonneg x)) (h _ (star_mul_self_nonneg x))

@[simp]
lemma norm_toPreGNS' (f : A →ₚ[ℂ] ℂ) (x : A) :
    ‖f.toPreGNS' x‖ = f.gnsSeminorm x := by
  simp [gnsSeminorm]

lemma gnsSeminorm_ofPreGNS' (f : A →ₚ[ℂ] ℂ) (x : f.PreGNS') :
    f.gnsSeminorm (f.ofPreGNS' x) = ‖x‖ := by
  rw [← norm_toPreGNS']
  simp

lemma cauchy_schwarz_star_mul (f : A →ₚ[ℂ] ℂ) (x y : A) :
    ‖f (star x * y)‖ ≤ √‖f (star x * x)‖ * √‖f (star y * y)‖ := by
  simpa [preGNS'_inner_def, preGNS'_norm_def'] using!
    norm_inner_le_norm (f.toPreGNS' x) (f.toPreGNS' y)

lemma cauchy_schwarz_mul_star (f : A →ₚ[ℂ] ℂ) (x y : A) :
    ‖f (x * star y)‖ ≤ √‖f (x * star x)‖ * √‖f (y * star y)‖ := by
  simpa using cauchy_schwarz_star_mul f (star x) (star y)

/-- If an element has zero GNS seminorm, every positive-functional coefficient with that
element in the first variable vanishes. -/
lemma apply_star_mul_eq_zero_of_apply_star_mul_self_eq_zero_left
    (f : A →ₚ[ℂ] ℂ) {x : A} (hx : f (star x * x) = 0) (y : A) :
    f (star x * y) = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm (f.cauchy_schwarz_star_mul x y |>.trans_eq ?_) (norm_nonneg _)
  rw [hx, norm_zero, Real.sqrt_zero, zero_mul]

/-- If an element has zero GNS seminorm, every positive-functional coefficient with that
element in the second variable vanishes. -/
lemma apply_star_mul_eq_zero_of_apply_star_mul_self_eq_zero_right
    (f : A →ₚ[ℂ] ℂ) {x : A} (hx : f (star x * x) = 0) (y : A) :
    f (star y * x) = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm (f.cauchy_schwarz_star_mul y x |>.trans_eq ?_) (norm_nonneg _)
  rw [hx, norm_zero, Real.sqrt_zero, mul_zero]

end CauchySchwarz

section NullIdeal

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The GNS null left ideal of a positive linear functional: the elements `x` for which
`φ (star x * x) = 0`. -/
def nullIdeal (φ : A →ₚ[ℂ] ℂ) : Ideal A where
  carrier := {x | φ (star x * x) = 0}
  zero_mem' := by simp
  add_mem' {x y} hx hy := by
    change φ (star x * x) = 0 at hx
    change φ (star y * y) = 0 at hy
    change φ (star (x + y) * (x + y)) = 0
    have hxy := φ.apply_star_mul_eq_zero_of_apply_star_mul_self_eq_zero_left hx y
    have hyx := φ.apply_star_mul_eq_zero_of_apply_star_mul_self_eq_zero_left hy x
    simp only [star_add, add_mul, mul_add, map_add, hx, hy, hxy, hyx, add_zero]
  smul_mem' a x hx := by
    change φ (star x * x) = 0 at hx
    change φ (star (a * x) * (a * x)) = 0
    have h := φ.apply_star_mul_eq_zero_of_apply_star_mul_self_eq_zero_left hx
      (star a * a * x)
    simpa only [smul_eq_mul, star_mul, mul_assoc] using h

@[simp]
lemma mem_nullIdeal (φ : A →ₚ[ℂ] ℂ) (x : A) :
    x ∈ φ.nullIdeal ↔ φ (star x * x) = 0 :=
  Iff.rfl

/-- Membership in the GNS null ideal is equivalent to the vanishing of every coefficient with
the null element in the second variable. -/
lemma mem_nullIdeal_iff_forall_apply_star_mul_eq_zero (φ : A →ₚ[ℂ] ℂ) (x : A) :
    x ∈ φ.nullIdeal ↔ ∀ y : A, φ (star y * x) = 0 := by
  constructor
  · intro hx y
    exact φ.apply_star_mul_eq_zero_of_apply_star_mul_self_eq_zero_right hx y
  · intro hx
    exact hx x

end NullIdeal

section GNSCoefficients

open scoped InnerProductSpace
open ContinuousLinearMap UniformSpace Completion Topology Set

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The GNS seminorm is continuous with respect to the C-star-algebra norm. -/
theorem gnsSeminorm_le_sqrt_opNorm_mul_norm (φ : A →ₚ[ℂ] ℂ) (x : A) :
    φ.gnsSeminorm x ≤ √‖φ.toContinuousLinearMap‖ * ‖x‖ := by
  rw [φ.gnsSeminorm_apply]
  have hx := φ.toContinuousLinearMap.le_opNorm (star x * x)
  change ‖φ (star x * x)‖ ≤ _ at hx
  grw [hx]
  rw [CStarRing.norm_star_mul_self, Real.sqrt_mul (norm_nonneg _),
    show √(‖x‖ * ‖x‖) = ‖x‖ by rw [← sq, Real.sqrt_sq (norm_nonneg x)]]

/-- The canonical map from a C-star algebra into the completion of its GNS pre-inner-product
space. -/
noncomputable def toGNS' (φ : A →ₚ[ℂ] ℂ) : A →L[ℂ] Completion φ.PreGNS' :=
  ((toComplL : φ.PreGNS' →L[ℂ] Completion φ.PreGNS').toLinearMap.comp
      φ.toPreGNS'.toLinearMap).mkContinuous √‖φ.toContinuousLinearMap‖ fun x => by
    rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
    change ‖(φ.toPreGNS' x : Completion φ.PreGNS')‖ ≤ _
    simpa using φ.gnsSeminorm_le_sqrt_opNorm_mul_norm x

@[simp]
lemma toGNS'_apply (φ : A →ₚ[ℂ] ℂ) (x : A) :
    φ.toGNS' x = (φ.toPreGNS' x : Completion φ.PreGNS') := rfl

theorem norm_toGNS'_le (φ : A →ₚ[ℂ] ℂ) :
    ‖φ.toGNS'‖ ≤ √‖φ.toContinuousLinearMap‖ := by
  apply LinearMap.mkContinuous_norm_le
  positivity

/-- GNS coefficient functionals parameterized continuously by the completed GNS space. -/
noncomputable def gnsCoefficientMap (φ : A →ₚ[ℂ] ℂ) :
    Completion φ.PreGNS' →L⋆[ℂ] (A →L[ℂ] ℂ) :=
  ((ContinuousLinearMap.compL ℂ A (Completion φ.PreGNS') ℂ).flip φ.toGNS').comp
    (innerSL ℂ)

@[simp]
lemma gnsCoefficientMap_apply (φ : A →ₚ[ℂ] ℂ) (z : Completion φ.PreGNS') (x : A) :
    φ.gnsCoefficientMap z x = ⟪z, φ.toGNS' x⟫_ℂ := by
  rw [gnsCoefficientMap]
  rfl

/-- The continuous conjugate-linear map sending `y` to the GNS coefficient functional
`x ↦ φ (star y * x)`. -/
noncomputable def gnsCoefficient (φ : A →ₚ[ℂ] ℂ) : A →L⋆[ℂ] (A →L[ℂ] ℂ) :=
  φ.gnsCoefficientMap.comp φ.toGNS'

@[simp]
lemma gnsCoefficient_apply (φ : A →ₚ[ℂ] ℂ) (y x : A) :
    φ.gnsCoefficient y x = φ (star y * x) := by
  rw [gnsCoefficient]
  change φ.gnsCoefficientMap (φ.toGNS' y) x = _
  rw [gnsCoefficientMap_apply]
  simp only [toGNS'_apply]
  rw [UniformSpace.Completion.inner_coe, preGNS'_inner_def, ofPreGNS'_toPreGNS',
    ofPreGNS'_toPreGNS']

@[simp]
lemma gnsCoefficientMap_coe (φ : A →ₚ[ℂ] ℂ) (y : A) :
    φ.gnsCoefficientMap (φ.toPreGNS' y : Completion φ.PreGNS') = φ.gnsCoefficient y := by
  rw [← toGNS'_apply]
  rfl

/-- A functional dominated by a GNS seminorm is represented by a vector in the completed GNS
space. -/
theorem exists_eq_gnsCoefficientMap_of_bound (φ : A →ₚ[ℂ] ℂ)
    (f : A →L[ℂ] ℂ) (C : ℝ) (hf : ∀ x, ‖f x‖ ≤ C * φ.gnsSeminorm x) :
    ∃ z, f = φ.gnsCoefficientMap z := by
  let fGNS : φ.PreGNS' →L[ℂ] ℂ :=
    (f.toLinearMap.comp φ.ofPreGNS'.toLinearMap).mkContinuous C fun x => by
      rw [← φ.gnsSeminorm_ofPreGNS' x]
      exact hf (φ.ofPreGNS' x)
  let fGNSCompletion : Completion φ.PreGNS' →L[ℂ] ℂ :=
    (innerSL ℂ (1 : Completion ℂ)).comp fGNS.completion
  let z : Completion φ.PreGNS' :=
    (InnerProductSpace.toDual ℂ (Completion φ.PreGNS')).symm fGNSCompletion
  refine ⟨z, ?_⟩
  ext x
  rw [gnsCoefficientMap_apply, InnerProductSpace.toDual_symm_apply]
  simp only [fGNSCompletion, ContinuousLinearMap.comp_apply, toGNS'_apply,
    ContinuousLinearMap.completion_apply_coe, fGNS, LinearMap.mkContinuous_apply,
    LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, ofPreGNS'_toPreGNS']
  change f x = ⟪(1 : Completion ℂ), (f x : Completion ℂ)⟫_ℂ
  rw [← UniformSpace.Completion.coe_one, UniformSpace.Completion.inner_coe,
    RCLike.inner_apply]
  simp

/-- Every coefficient parameterized by the completed GNS space is a norm limit of
coefficients parameterized by elements of the algebra. -/
theorem gnsCoefficientMap_mem_closure_range (φ : A →ₚ[ℂ] ℂ)
    (z : Completion φ.PreGNS') :
    φ.gnsCoefficientMap z ∈ closure (range φ.gnsCoefficient) := by
  apply map_mem_closure φ.gnsCoefficientMap.continuous
    (UniformSpace.Completion.denseRange_coe z)
  rintro _ ⟨y, rfl⟩
  exact ⟨φ.ofPreGNS' y, by
    rw [← φ.gnsCoefficientMap_coe]
    simp⟩

/-- A functional dominated by a GNS seminorm lies in the operator-norm closure of the GNS
coefficient functionals. -/
theorem mem_closure_range_gnsCoefficient_of_bound (φ : A →ₚ[ℂ] ℂ)
    (f : A →L[ℂ] ℂ) (C : ℝ) (hf : ∀ x, ‖f x‖ ≤ C * φ.gnsSeminorm x) :
    f ∈ closure (range φ.gnsCoefficient) := by
  obtain ⟨z, rfl⟩ := φ.exists_eq_gnsCoefficientMap_of_bound f C hf
  exact φ.gnsCoefficientMap_mem_closure_range z

end GNSCoefficients
end PositiveLinearMap

namespace PositiveContinuousLinearMap
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem norm_apply_le_sqrt_opNorm_mul (f : A →P[ℂ] ℂ) (x : A) :
    ‖f x‖ ≤ √‖(f : A →L[ℂ] ℂ)‖ * √‖f (star x * x)‖ := by
  have hl := CStarAlgebra.increasingApproximateUnit A
  refine le_of_tendsto ((ContinuousAt.tendsto (by fun_prop)).comp (hl.tendsto_mul_right _)).norm ?_
  filter_upwards [hl.eventually_nonneg, hl.eventually_norm] with e he1 he2
  grw [← he1.star_eq, Function.comp_apply, ← f.coe_toPositiveLinearMap,
    f.toPositiveLinearMap.cauchy_schwarz_star_mul, f.coe_toPositiveLinearMap,
    ← f.coe_toContinuousLinearMap, f.toContinuousLinearMap.le_opNorm (star e * e),
    CStarRing.norm_star_mul_self, he2, he2, one_mul, mul_one]

open Topology Complex in
theorem tendsto_nhds_opNorm (f : A →P[ℂ] ℂ) {l : Filter A} (hl : l.IsIncreasingApproximateUnit) :
    l.Tendsto (f ·) (𝓝 ‖(f : A →L[ℂ] ℂ)‖) := by
  suffices l.Tendsto (‖f ·‖) (𝓝 ‖(f : A →L[ℂ] ℂ)‖) from this.ofReal.congr' <| by
    filter_upwards [hl.eventually_nonneg] using by simp_all [norm_of_nonneg' (f.map_nonneg _)]
  refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
  have h : ∀ᶠ x in l, ‖f x‖ ≤ ‖(f : A →L[ℂ] ℂ)‖ + ε / 2 := by
    filter_upwards [hl.eventually_norm] with x hx
    grw [← f.coe_toContinuousLinearMap, ContinuousLinearMap.le_opNorm, hx, mul_one]
    grind
  have h2 : ∀ᶠ x in l, ‖(f : A →L[ℂ] ℂ)‖ - ε / 2 < ‖f x‖ := by
    obtain ⟨_, ⟨a, ha1, rfl⟩, ha2⟩ := exists_lt_of_lt_csSup (b := ‖(f : A →L[ℂ] ℂ)‖ - ε / 4)
      ((Metric.nonempty_closedBall (x := 0).mpr zero_le_one).image (‖f ·‖))
      (by rw [← f.toContinuousLinearMap.sSup_unitClosedBall_eq_norm]; simp; grind)
    have h3 : ∀ᶠ x in l, ‖f (x * a)‖ ^ 2 ≤ ‖f x‖ * ‖(f : A →L[ℂ] ℂ)‖ := by
      filter_upwards [hl.eventually_nonneg, hl.eventually_norm] with x hx1 hx2
      have : ‖f (star x * x)‖ ≤ ‖f x‖ := by
        refine CStarAlgebra.norm_le_norm_of_nonneg_of_le (f.map_nonneg (star_mul_self_nonneg _)) ?_
        exact f.mono <| hx1.star_eq.symm ▸ CStarAlgebra.mul_self_le_of_nonneg_of_norm_le_one hx1 hx2
      conv_lhs => rw [← hx1.star_eq, ← f.coe_toPositiveLinearMap]
      grw [f.cauchy_schwarz_star_mul x a, mul_pow, Real.sq_sqrt (norm_nonneg _),
        Real.sq_sqrt (norm_nonneg _), f.coe_toPositiveLinearMap, this,
        ← f.coe_toContinuousLinearMap, f.toContinuousLinearMap.le_opNorm (star a * a),
        CStarRing.norm_star_mul_self, ← mul_assoc]
      refine mul_le_of_le_one_right (by positivity) ?_
      grw [mem_closedBall_zero_iff.mp ha1, mem_closedBall_zero_iff.mp ha1, one_mul]
    have h4 : ∀ᶠ x in l, ‖(f : A →L[ℂ] ℂ)‖ - ε / 4 < ‖f (x * a)‖ := by
      refine (Filter.Tendsto.norm ?_).eventually (lt_mem_nhds ha2)
      exact (ContinuousAt.tendsto (by fun_prop)).comp (hl.tendsto_mul_right a)
    filter_upwards [h3, h4] with x _ _ using by nlinarith [norm_nonneg (f x)]
  filter_upwards [h, h2] using by grind [Real.dist_eq]

theorem ofReal_opNorm_eq_map_one {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (f : A →P[ℂ] ℂ) : ‖(f : A →L[ℂ] ℂ)‖ = f 1 :=
  tendsto_nhds_unique (f.tendsto_nhds_opNorm (.pure_one A)) (tendsto_pure_nhds _ _)

end PositiveContinuousLinearMap

namespace ContinuousLinearMap
variable {A} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {f : A →L[ℂ] ℂ}

open Topology Filter Complex CStarRing

private lemma im_apply_eq_zero_of_tendsto_nhds_opNorm {l : Filter A}
    (hl : l.IsIncreasingApproximateUnit) (hf : l.Tendsto (f ·) (𝓝 ‖f‖)) {a : A}
    (ha : IsSelfAdjoint a) : (f a).im = 0 := by
  by_cases ‖f‖ = 0
  · simp_all
  suffices ∀ (t : ℝ), ‖f a + I * t * ‖f‖‖ ^ 2 ≤ ‖f‖ ^ 2 * (‖a‖ ^ 2 + t ^ 2) by
    contrapose! this
    refine ⟨(‖f‖ ^ 2 * ‖a‖ ^ 2 - ‖f a‖ ^ 2 + 1) / (2 * (f a).im * ‖f‖), ?_⟩
    simp [normSq, ← normSq_eq_norm_sq, -ofReal_div]; field_simp; grind
  intro t
  suffices (fun x ↦ ‖f (a + (I * t) • x)‖ ^ 2) ≤ᶠ[l]
        (fun x ↦ ‖f‖ ^ 2 * (‖a‖ ^ 2 + t ^ 2 + |t| * ‖a * x - x * a‖)) by
    refine le_of_tendsto_of_tendsto (hb := hl.neBot) ?_ ?_ this
    · simp_rw [map_add, map_smul, smul_eq_mul]
      apply_rules [Tendsto.pow, Tendsto.norm, Tendsto.const_add, Tendsto.const_mul]
    · simpa using (hl.tendsto_mul_left a).sub (hl.tendsto_mul_right a)
        |>.norm |>.const_mul _ |>.const_add _ |>.const_mul _
  filter_upwards [hl.eventually_isSelfAdjoint, hl.eventually_norm] with x hx hx2
  grw [f.le_opNorm, mul_pow, mul_le_mul_iff_of_pos_left (by simp_all), sq, ← norm_star_mul_self]
  calc
    _ = ‖a * a + (t ^ 2 : ℂ) • (x * x) + (I * t) • (a * x + -(x * a))‖ := by
      simp [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, mul_mul_mul_comm]
      grind [sq]
  _ ≤ ‖a‖ ^ 2 + t ^ 2 + |t| * ‖a * x - x * a‖ := by
      grw [add_assoc, sq, norm_add_le, norm_add_le, ← sub_eq_add_neg, sq, ← norm_star_mul_self,
        add_assoc, ha.star_eq, add_le_add_iff_left, norm_smul, norm_mul_le x, hx2, hx2]
      simp [norm_smul, sq]

theorem monotone_iff_tendsto_nhds_opNorm {l : Filter A} (hl : l.IsIncreasingApproximateUnit) :
    Monotone f ↔ l.Tendsto (f ·) (𝓝 ‖f‖) := by
  refine ⟨fun hf ↦ ?_, fun hf ↦ monotone_iff_map_nonneg _ |>.mpr fun a ha ↦ ?_⟩
  · exact ({ __ := f, monotone' := hf } : _ →P[ℂ] _).tendsto_nhds_opNorm hl
  by_cases ha0 : a = 0
  · simp [ha0]
  suffices 0 ≤ (f (‖a‖⁻¹ • a)).re by simpa [Complex.le_def, ha0,
    im_apply_eq_zero_of_tendsto_nhds_opNorm hl hf ha.isSelfAdjoint] using this
  suffices ‖‖f‖ - f (‖a‖⁻¹ • a)‖ ≤ ‖f‖ by grw [← re_le_norm] at this; simpa
  refine le_of_tendsto (hx := hl.neBot) (hf.sub_const (f _) |>.norm) ?_
  filter_upwards [hl.eventually_nonneg, hl.eventually_norm] with y hy hy2
  grw [← map_sub, f.le_opNorm, CStarAlgebra.norm_sub_le_one_of_nonneg_of_norm_le_one hy hy2
    (by simp [smul_nonneg, ha]) (by simp [norm_smul, ha0]), mul_one]

theorem monotone_iff_opNorm_eq_map_one {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] {f : A →L[ℂ] ℂ} : Monotone f ↔ ‖f‖ = f 1 := by
  rw [f.monotone_iff_tendsto_nhds_opNorm (.pure_one A)]
  have := tendsto_pure_nhds f 1
  exact ⟨fun h ↦ tendsto_nhds_unique h this, fun h ↦ by simpa [h]⟩

end ContinuousLinearMap
