module

public import LeanOA.Mathlib.Topology.Algebra.Module.PolarTopology

@[expose] public section

open scoped ComplexOrder
open WeakBilin

open Set Filter Bornology

variable {𝕜 E F : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

/-- The Mackey topology on a space `E` relative to a bilinear form `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜` is the
polar topology corresponding to all (weakly) compact absolutely convex sets in `F`.

Although it is not required for the definition, the space `F` should be equipped with the weak
topology induced by `B.flip` for any of the usual theorems to be applicable. -/
abbrev Mackey (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) :=
    PolarTopology B {s | IsCompact s ∧ AbsConvex 𝕜 s}

variable {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜}

variable (B) in
/-- The identity map from `E` to its type synonym equipped with the Mackey topology. -/
noncomputable def toMackey : E ≃ₗ[𝕜] Mackey B := PolarTopology.linearEquiv.symm

/-- The identity map from the type synonym `Mackey B` back to `E` with its original topology. -/
noncomputable def ofMackey : Mackey B ≃ₗ[𝕜] E := PolarTopology.linearEquiv

@[simp]
lemma ofMackey_symm : ofMackey.symm = toMackey B := rfl

@[simp]
lemma toMackey_symm : (toMackey B).symm = ofMackey := rfl

@[simp]
lemma toMackey_ofMackey (x : Mackey B) : toMackey B (ofMackey x) = x := rfl

@[simp]
lemma ofMackey_toMackey (x : E) : ofMackey (toMackey B x) = x := rfl

theorem nonempty_setOf_isCompact_absConvex (𝕜 F : Type*) [NormedField 𝕜]
    [PartialOrder 𝕜] [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] :
    (Set.Nonempty {s : Set F | IsCompact s ∧ AbsConvex 𝕜 s}) :=
  ⟨∅, isCompact_empty, .empty⟩

theorem directedOn_setOf_isCompact_absConvex (𝕜 F : Type*) [RCLike 𝕜]
    [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [ContinuousSMul 𝕜 F] [T2Space F] :
    DirectedOn (· ⊆ ·) {s : Set F | IsCompact s ∧ AbsConvex 𝕜 s} := by
  rintro s ⟨hs₁, hs₂⟩ t ⟨ht₁, ht₂⟩
  refine ⟨closedAbsConvexHull 𝕜 (convexHull 𝕜 (s ∪ t)), ⟨?_, absConvex_convexClosedHull⟩,
    ?hs, ?ht⟩
  case hs | ht => intro; grw [← subset_closedAbsConvexHull, ← subset_convexHull]; simp_all
  exact hs₁.convexHull_union ht₁ hs₂.2 ht₂.2 |>.closedAbsConvexHull (convex_convexHull 𝕜 _)

open ContinuousLinearMap Module in
open scoped Topology in
/-- If `s` is a basis of neighborhoods of zero, the continuous dual is the union of the polars of
the sets `s i`. This is Theorem 3.2 in Voigt, *Topological Vector Spaces*. -/
lemma StrongDual.range_coeLM_eq_sUnion_polar_nhds {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] {ι : Sort*} {p : ι → Prop} {s : ι → Set E}
    (h : (𝓝 0).HasBasis p s) :
    (coeLM 𝕜 : StrongDual 𝕜 E →ₗ[𝕜] Dual 𝕜 E).range =
      ⋃₀ {(LinearMap.id (R := 𝕜) (M := Dual 𝕜 E)).flip.polar (s i) | (i : ι) (_ : p i)} := by
  ext f
  simp only [SetLike.mem_coe, LinearMap.mem_range, coeLM_apply, exists_prop, Set.mem_sUnion,
    Set.mem_setOf_eq, exists_exists_and_eq_and]
  constructor
  · rintro ⟨y, rfl⟩
    have := ContinuousAt.tendsto <| map_continuousAt y 0
    simp only [map_zero, LinearMap.polar, LinearMap.flip_apply, LinearMap.id_coe, id_eq,
      Set.mem_setOf_eq, coe_coe] at this ⊢
    convert Filter.Tendsto.basis_left this h (Metric.closedBall 0 1)
      <| Metric.closedBall_mem_nhds _ zero_lt_one
    simp only [Metric.closedBall, dist_zero_right, Set.MapsTo, Set.mem_setOf_eq]
  · rintro ⟨i, hi_p, hi⟩
    have : s i ∈ 𝓝 0 := by
      apply h.1 (s i) |>.mpr
      exact ⟨i, hi_p, Subset.rfl⟩
    exact ⟨LinearMap.clmOfExistsBoundedImage f
      ⟨s i, this, Bornology.isVonNBounded_image _ _ hi⟩, rfl⟩

namespace Mackey

variable (B)
variable [B.flip.IsWeak]

instance [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [T1Space F] :
    LocallyConvexSpace ℝ (Mackey B) :=
  have := LinearMap.IsWeak.isTopologicalAddGroup B.flip
  have := LinearMap.IsWeak.continuousSMul B.flip
  PolarTopology.locallyConvexSpace (nonempty_setOf_isCompact_absConvex 𝕜 _)
    (directedOn_setOf_isCompact_absConvex 𝕜 _) fun _ h ↦ h.1.isVonNBounded 𝕜

instance [T1Space F] : LocallyConvexSpace 𝕜 (Mackey B) :=
  let _ : Module ℝ E := RestrictScalars.module ℝ 𝕜 E
  let _ : IsScalarTower ℝ 𝕜 E := RestrictScalars.isScalarTower ℝ 𝕜 E
  .to_rclike 𝕜 (Mackey B) inferInstance

/-- Every compact set gives rise to a seminorm on `Mackey B`, but in practice we are only interested
in those for which the sets are also absolutely convex. -/
noncomputable abbrev seminorm (s : Set F) (hs : IsCompact s) :
    Seminorm 𝕜 (Mackey B) :=
  PolarTopology.seminorm B {s | IsCompact s ∧ AbsConvex 𝕜 s} s <| by
    let _ := LinearMap.IsWeak.isTopologicalAddGroup B.flip
    let _ := LinearMap.IsWeak.continuousSMul B.flip
    exact hs.isVonNBounded 𝕜

/-- The compact absolutely convex sets give rise to a seminorm family on `Mackey B` which induces
the topology. -/
noncomputable abbrev seminormFamily :
    SeminormFamily 𝕜 (Mackey B) {s : Set F | IsCompact s ∧ AbsConvex 𝕜 s} :=
  PolarTopology.seminormFamily B {s | IsCompact s ∧ AbsConvex 𝕜 s}
    fun _ hs ↦ by
      let _ := LinearMap.IsWeak.isTopologicalAddGroup B.flip
      let _ := LinearMap.IsWeak.continuousSMul B.flip
      exact hs.1.isVonNBounded 𝕜

lemma continuous_seminorm [T1Space F] (s : Set F) (hs₁ : IsCompact s) (hs₂ : AbsConvex 𝕜 s) :
    Continuous (seminorm B s hs₁) :=
  have := LinearMap.IsWeak.isTopologicalAddGroup B.flip
  have := LinearMap.IsWeak.continuousSMul B.flip
  PolarTopology.continuous_seminorm (nonempty_setOf_isCompact_absConvex 𝕜 F)
    (directedOn_setOf_isCompact_absConvex 𝕜 F) _ ⟨hs₁, hs₂⟩ (hs₁.isVonNBounded 𝕜)

lemma directed_seminormFamily [T1Space F] : Directed (· ≤ ·) (seminormFamily B) :=
  have := LinearMap.IsWeak.isTopologicalAddGroup B.flip
  have := LinearMap.IsWeak.continuousSMul B.flip
  PolarTopology.directed_seminormFamily (fun _ hs ↦ hs.1.isVonNBounded 𝕜)
    (directedOn_setOf_isCompact_absConvex 𝕜 F)

lemma withSeminorms [T1Space F] : WithSeminorms (seminormFamily B) :=
  have := LinearMap.IsWeak.isTopologicalAddGroup B.flip
  have := LinearMap.IsWeak.continuousSMul B.flip
  PolarTopology.withSeminorms B _ (nonempty_setOf_isCompact_absConvex 𝕜 F)
    (directedOn_setOf_isCompact_absConvex 𝕜 F) fun _ hs ↦ hs.1.isVonNBounded 𝕜

end Mackey

variable (B)
variable [B.flip.IsWeak]

open PolarTopology in
/-- Every compatible locally convex topology is weaker than the Mackey topology. -/
lemma continuous_ofMackey [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
    [LocallyConvexSpace 𝕜 E] [B.IsCompatibleDual] :
    Continuous (ofMackey : Mackey B → E) := by
  refine polarTopologyNhdsPolars.continuous.comp <|
    continuous_mono B B.nhdsPolars {s | IsCompact s ∧ AbsConvex 𝕜 s} ?_
  rintro - ⟨s, hs, rfl⟩
  exact ⟨LinearMap.IsCompatibleDual.isCompact_polar B hs, B.absConvex_polar s⟩

/-- The map `⇑ofMackey : Mackey 𝕜 E → E` as a continuous linear map. -/
noncomputable def ofMackeyCLM [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
    [LocallyConvexSpace 𝕜 E] [B.IsCompatibleDual] :
    Mackey B →L[𝕜] E where
  toLinearMap := ofMackey.toLinearMap
  cont := continuous_ofMackey B

open PolarTopology in
theorem isWeak_bilin :
    (bilin B {s | IsCompact s ∧ AbsConvex 𝕜 s}).IsWeak := by
  apply LinearMap.IsWeak.congr B.flip (e := ContinuousLinearEquiv.refl 𝕜 F) (f := toMackey B)
  aesop

open ContinuousLinearMap Module PolarTopology Pointwise LinearMap in
theorem Mackey.range_coeLM_eq_image_bilin [Module ℝ F] [IsScalarTower ℝ 𝕜 F] [T1Space F] :
    (coeLM 𝕜 : StrongDual 𝕜 (Mackey B) →ₗ[𝕜] Dual 𝕜 (Mackey B)).range =
      (bilin B {s | IsCompact s ∧ AbsConvex 𝕜 s}) '' univ := by
  letI B₁ := bilin B {s | IsCompact s ∧ AbsConvex 𝕜 s}
  letI := LinearMap.IsWeak.isTopologicalAddGroup B.flip
  letI := LinearMap.IsWeak.continuousSMul B.flip
  letI : ContinuousSMul ℝ F := IsScalarTower.continuousSMul 𝕜
  letI : ContinuousSMul 𝕜 (Mackey B) := by
    apply PolarTopology.continuousSMul (B := B)
    exact fun _ hS ↦ IsCompact.isVonNBounded 𝕜 hS.1
  letI := isWeak_bilin B
  rw [StrongDual.range_coeLM_eq_sUnion_polar_nhds (𝕜 := 𝕜) (E := Mackey B) <|
      hasBasis_nhds_zero_polar (nonempty_setOf_isCompact_absConvex _ _)
        (directedOn_setOf_isCompact_absConvex _ _)
        (by simpa [mem_setOf_eq, and_imp] using fun _ h _ ↦ IsCompact.isVonNBounded _ h)
        (fun c _ w hw ↦ ⟨c • w, ⟨⟨IsCompact.smul _ hw.1, by
                simpa using AbsConvex.image (Module.End.smulLeft (RCLike.ofReal _)
                  (algebraMap_mem_center _)) hw.2⟩, by aesop⟩⟩)]
  ext x
  constructor
  · simp only [mem_setOf_eq, exists_prop, mem_sUnion, exists_exists_and_eq_and]
    rintro ⟨s, _, hb⟩
    by_cases hne : s.Nonempty
    · rw [Module.dualPairing_flip_polar_polar B₁ (by aesop) (by aesop) hne] at hb
      grind
    · simp only [image_univ, Set.mem_range, not_nonempty_iff_eq_empty.mp hne , polar_empty] at hb ⊢
      rw [polar_univ, mem_singleton_iff] at hb
      · use 0; rw [hb, map_zero]
      exact separatingRight_iff_flip_ker_eq_bot.mpr rfl
  · simp only [image_univ, Set.mem_range, mem_setOf_eq, exists_prop, mem_sUnion,
    exists_exists_and_eq_and, forall_exists_index]
    intro f hf
    use closedAbsConvexHull 𝕜 (convexHull ℝ {f})
    have hcpt : IsCompact <| closedAbsConvexHull 𝕜 (convexHull ℝ {f}) := by
      apply IsCompact.closedAbsConvexHull <| Set.Finite.isCompact_convexHull _
        Finite.of_subsingleton
      rw [← convexHull_rclike_eq_convexHull_real (K := 𝕜)]
      exact convex_convexHull ..
    exact ⟨⟨hcpt, absConvex_convexClosedHull⟩, by
      rw [Module.dualPairing_flip_polar_polar B₁ absConvex_convexClosedHull hcpt
        (by simp [convexHull_singleton, closedAbsConvexHull_eq_closure_absConvexHull,
         closure_nonempty_iff, absConvexHull_nonempty, singleton_nonempty])]
      exact ⟨f, by simpa [closedAbsConvexHull_eq_closure_absConvexHull] using subset_closure <|
           (mem_absConvexHull_iff.mpr fun _ a _ ↦ a rfl : f ∈ absConvexHull 𝕜 {_}), hf⟩⟩

open ContinuousLinearMap Module PolarTopology Pointwise LinearMap in
theorem Mackey.range_coeLM_eq_range_bilin [Module ℝ F] [IsScalarTower ℝ 𝕜 F] [T1Space F] :
    (bilin B {s | IsCompact s ∧ AbsConvex 𝕜 s}).range =
      (coeLM 𝕜 : StrongDual 𝕜 (Mackey B) →ₗ[𝕜] Dual 𝕜 (Mackey B)).range := by
  have : (bilin B {s | IsCompact s ∧ AbsConvex 𝕜 s}).range =
      (bilin B {s | IsCompact s ∧ AbsConvex 𝕜 s}) '' univ := by
    ext; simp
  have h2 := Mackey.range_coeLM_eq_image_bilin B
  rw [← this] at h2
  exact_mod_cast h2.symm

open ContinuousLinearMap Module PolarTopology Pointwise LinearMap in
/-- The topology on `Mackey B` is compatible with the type-appropriate version of `B`. -/
instance [Module ℝ F] [IsScalarTower ℝ 𝕜 F] [T1Space F] :
    (bilin B {s | IsCompact s ∧ AbsConvex 𝕜 s}).flip.IsCompatibleDual where
  range_eq_range := Mackey.range_coeLM_eq_range_bilin B
  injective := by
    letI := LinearMap.IsWeak.isTopologicalAddGroup B.flip
    rw [LinearMap.flip_flip, ← LinearMap.ker_eq_bot]
    ext x
    constructor
    · intro hx
      simp only [LinearMap.mem_ker, LinearMap.ext_iff, LinearMap.flip_apply,
        LinearEquiv.arrowCongr_apply, LinearEquiv.symm_symm, LinearEquiv.refl_apply,
        LinearMap.zero_apply, Submodule.mem_bot] at hx ⊢
      apply (flip_separatingLeft.mp <| IsWeak.separatingLeft_of_t1Space B.flip) x
      exact hx
    · intro hx
      simp at hx
      aesop

namespace Mackey

variable {E' : Type*} [AddCommGroup E'] [Module 𝕜 E']
  {B' : E' →ₗ[𝕜] F →ₗ[𝕜] 𝕜} [B'.flip.IsWeak]

/-- Pairing-preserving linear equivalences in the left coordinate induce continuous linear
equivalences between the corresponding Mackey spaces. -/
noncomputable def congrLeft (e : E ≃ₗ[𝕜] E') (h : ∀ x y, B' (e x) y = B x y) :
    Mackey B ≃L[𝕜] Mackey B' :=
  PolarTopology.congrLeft B {s | IsCompact s ∧ AbsConvex 𝕜 s} e h

@[simp]
lemma congrLeft_apply (e : E ≃ₗ[𝕜] E') (h : ∀ x y, B' (e x) y = B x y)
    (x : Mackey B) :
    congrLeft B e h x = toMackey B' (e (ofMackey x)) :=
  rfl

@[simp]
lemma congrLeft_symm_apply (e : E ≃ₗ[𝕜] E') (h : ∀ x y, B' (e x) y = B x y)
    (x : Mackey B') :
    (congrLeft B e h).symm x = toMackey B (e.symm (ofMackey x)) :=
  rfl

end Mackey
