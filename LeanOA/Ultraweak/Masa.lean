module

public import LeanOA.ExtremallyDisconnected
public import LeanOA.Masa
public import LeanOA.CStarAlgebra.RealRankZero
public import LeanOA.Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import LeanOA.Ultraweak.LUB
public import LeanOA.Ultraweak.WStarAlgebra
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
public import Mathlib.Analysis.CStarAlgebra.Unitary.Span

@[expose] public section

/-!
# Maximal abelian subalgebras of algebras with a predual

An ambient predual supplies monotone completeness to a masa. Transport through the Gelfand
transform then makes its character space extremally disconnected, which in turn yields norm
density of real linear combinations of projections among self-adjoint elements.
-/

variable {M P : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]

open scoped Ultraweak


variable (M P) in
/-- Instance of `ConditionallyCompletePartialOrderSup`. -/
noncomputable abbrev WStarAlgebra.instCCPO : ConditionallyCompletePartialOrderSup M :=
  inferInstanceAs (ConditionallyCompletePartialOrderSup σ(M, P))

open WeakDual ContinuousMap

section StarMemClass

@[simp]
lemma SetLike.isSelfAdjoint_iff {S R : Type*} [Star R] [SetLike S R] [StarMemClass S R]
    {s : S} {x : s} : IsSelfAdjoint (x : R) ↔ IsSelfAdjoint x := by
  simp [IsSelfAdjoint, Subtype.ext_iff]

end StarMemClass

namespace StarSubalgebra

open Submodule StarOrderedRing in
open scoped IsMulCommutative in
/-- A maximal abelian star subalgebra contains any ambient least upper bound of a nonempty family
of its self-adjoint elements. -/
lemma IsMasa.mem_of_isLUB (S : StarSubalgebra ℂ M) [S.IsMasa]
    {s : Set M} {u : M} (hsS : s ⊆ S) (hnon : s.Nonempty)
    (hsa : ∀ x ∈ s, IsSelfAdjoint x) (hu : IsLUB s u) : u ∈ S := by
  letI : IsStarNormal u :=
    (IsSelfAdjoint.of_ge (hu.1 hnon.some_mem) (hsa _ hnon.some_mem)).isStarNormal
  refine IsMasa.mem_of_commute _ (x := u) ?_
  suffices ∀ v ∈ span ℂ (S.toSubmodule.subtype '' (unitary S : Set S)), Commute u v by
    simp only [← map_span] at this
    simpa [CStarAlgebra.span_unitary S]
  suffices ∀ v ∈ unitary S, Commute u v from Commute.span_right (by simpa)
  intro v hv
  lift v to unitary S using hv
  refine .symm <| (commute_unitary_iff_star_right_conjugate
    (u := (Unitary.map (⟨S.subtype.toRingHom, by simp⟩ : S →⋆* M) v : M)) (by grind) |>.mpr ?_)
  have h_image : conjOrderHom (v : M) '' s = s := by
    convert Set.image_id s using 1
    apply Set.EqOn.image_eq
    intro x hx
    lift x to S using hsS hx
    simp [← MulMemClass.coe_mul, ← StarMemClass.coe_star,
      mul_comm (v : S), mul_assoc _ (v : S)]
  exact (h_image ▸ hu.conjugate_star_right_of_isUnit (v : M)
    (Unitary.toUnits v |>.map (SubmonoidClass.subtype S) |>.isUnit)).unique hu

include P in
open Submodule StarOrderedRing in
open scoped ComplexOrder IsMulCommutative in
lemma IsMasa.extremallyDisconnected_characterSpace_of_predual
    (S : StarSubalgebra ℂ M) [hS : S.IsMasa] :
    ExtremallyDisconnected (characterSpace ℂ S) := by
  /- Since `M` has a predual, it is a conditionally complete partial order.
  To show that `characterSpace ℂ S` is extremally disconnected, it suffices to prove that
  `C(characterSpace ℂ S, ℝ)` is monotone complete. Note that using `ℝ` instead of `ℂ` here is
  essential for the proof technique. So take a nonempty directed set `s` in
  `C(characterSpace ℂ S, ℝ)` which is bounded above; we will show it has a supremum.

  The Gelfand transform is a star algebra isomorphism (`e`)
  and an order isomorphism (`o`) between `S` and `C(characterSpace ℂ S, ℂ)`.
  We let `f` denote the composition of the maps
  `C(characterSpace ℂ S, ℝ) → C(characterSpace ℂ S, ℂ) → S → M`, which is monotone (and a
  star algebra homomorphism). As such the image `f '' s` is directed and bounded above.
  Since `M` is monotone complete, this set has a supremum `u`, which is selfadjoint because
  the elements of `f '' s` are. -/
  let _ := WStarAlgebra.instCCPO M P
  refine .ofConditionallyCompletePartialOrderSupContinuousMap
    (𝕜 := ℝ) fun s hs hnon hbdd ↦ ?_
  let e := gelfandStarTransform S
  let o : S ≃o C(characterSpace ℂ S, ℂ) := OrderIsoClass.toOrderIso e
  let (eq := hf_eq) f : C(characterSpace ℂ S, ℝ) → M := Subtype.val ∘ o.symm ∘ realToRCLike ℂ
  have hf : Monotone f := fun _ _ ↦ by simp [f]
  replace hs : DirectedOn (· ≤ ·) (f '' s) := hs.mono_comp hf
  replace hbdd : BddAbove (f '' s) := hf.map_bddAbove hbdd
  let u := ⨆ i : s, f i
  have hu : IsLUB (f '' s) u := hs.isLUB_ciSup_set hbdd hnon
  have hsa : ∀ x ∈ f '' s, IsSelfAdjoint x := by
    rintro _ ⟨g, -, rfl⟩
    exact isSelfAdjoint_realToRCLike (𝕜 := ℂ) (f := g) |>.map e.symm |>.map S.subtype
  have hu' : IsSelfAdjoint u :=
    .of_ge (hu.1 (hnon.image f).some_mem) (hsa _ (hnon.image f).some_mem)
  have hu_mem : u ∈ S := IsMasa.mem_of_isLUB S
    (by rintro _ ⟨g, -, rfl⟩; exact (o.symm (realToRCLike ℂ g)).property)
    (hnon.image f) hsa hu
  /- Since `u ∈ S`, is the supremum of a set of elements in `S`, applying the Gelfand transform
  we obtain the supremum of a collection of elements in `C(characterSpace ℂ S, ℂ)`. But since
  `u` is selfadjoint, so also is its image under the Gelfand transform, so we may realize this image
  as an element of `C(characterSpace ℂ S, ℝ)`, thereby obtaining our desired supremum. -/
  lift u to S using hu_mem with u
  rw [hf_eq, Function.comp_def (f := Subtype.val), ← Set.image_image (g := Subtype.val)] at hu
  replace hu := hu.of_image (by simp)
  rw [Function.comp_def (f := o.symm), ← Set.image_image (g := o.symm), o.symm.isLUB_image,
    o.symm_symm] at hu
  have : IsSelfAdjoint (o u) := .map (by simpa using hu') e
  exact ⟨_, (this.realToRCLike_rclikeToReal ▸ hu).of_image <| by simp⟩

end StarSubalgebra

include P in
/-- A C-star algebra with a specified Banach predual has real rank zero. -/
theorem CStarAlgebra.isRealRankZero_of_predual :
    CStarAlgebra.IsRealRankZero M :=
  CStarAlgebra.isRealRankZero_iff_spectrum.mpr fun x hx ↦ by
    letI : IsStarNormal x := hx.isStarNormal
    let B := StarAlgebra.adjoin ℂ ({x} : Set M)
    letI : IsMulCommutative B := inferInstance
    obtain ⟨S, hBS, hS⟩ := B.exists_le_isMasa
    letI : S.IsMasa := hS
    letI : CommCStarAlgebra S := IsMulCommutative.instCommCStarAlgebra
    have hxS : x ∈ S := hBS <| StarAlgebra.subset_adjoin ℂ ({x} : Set M) (by simp)
    let y : S := ⟨x, hxS⟩
    letI : ExtremallyDisconnected (characterSpace ℂ S) :=
      StarSubalgebra.IsMasa.extremallyDisconnected_characterSpace_of_predual (P := P) S
    letI : CStarAlgebra.IsRealRankZero S :=
      CStarAlgebra.IsRealRankZero.of_starAlgEquiv (gelfandStarTransform S)
    have hy : IsSelfAdjoint y := SetLike.isSelfAdjoint_iff.mp hx
    have hy' : y ∈ closure {z : S | IsSelfAdjoint z ∧ (spectrum ℝ z).Finite} :=
      CStarAlgebra.isRealRankZero_iff_spectrum.mp (by infer_instance) hy
    have hmap : Set.MapsTo (S.subtype : S → M)
        {z : S | IsSelfAdjoint z ∧ (spectrum ℝ z).Finite}
        {z : M | IsSelfAdjoint z ∧ (spectrum ℝ z).Finite} := fun z hz ↦
      ⟨hz.1.map S.subtype, hz.1.map_spectrum_real S.subtype Subtype.val_injective ▸ hz.2⟩
    simpa [y] using map_mem_closure continuous_subtype_val hy' hmap

include P in
/-- In a C⋆-algebra with a specified predual, every self-adjoint element is a norm limit of real
linear combinations of projections. -/
theorem IsSelfAdjoint.mem_topologicalClosure_span_isStarProjection_of_predual
    {x : M} (hx : IsSelfAdjoint x) :
    x ∈ closure (Submodule.span ℝ {p : M | IsStarProjection p} : Set M) :=
  let _ := CStarAlgebra.isRealRankZero_of_predual (M := M) (P := P)
  CStarAlgebra.IsRealRankZero.topologicalClosure_span_isStarProjection.ge hx

include P in
/-- In a C-star algebra with a specified Banach predual, every nonnegative element is a norm limit
of nonnegative real linear combinations of projections. -/
theorem CStarAlgebra.mem_topologicalClosure_hull_isStarProjection_of_predual
    {x : M} (hx : 0 ≤ x) :
    x ∈ closure (ConvexCone.hull ℝ {p : M | IsStarProjection p} : Set M) :=
  let _ := CStarAlgebra.isRealRankZero_of_predual (M := M) (P := P)
  CStarAlgebra.IsRealRankZero.mem_topologicalClosure_hull_isStarProjection hx

section WStarAlgebra

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [WStarAlgebra A]

noncomputable instance : CStarAlgebra.IsRealRankZero A :=
  CStarAlgebra.isRealRankZero_of_predual (P := WStarAlgebra.predual A)

namespace StarSubalgebra

/-- The character space of a maximal abelian star subalgebra of a W-star algebra is extremally
disconnected. -/
lemma IsMasa.extremallyDisconnected_characterSpace (S : StarSubalgebra ℂ A) [S.IsMasa] :
    ExtremallyDisconnected (characterSpace ℂ S) :=
  IsMasa.extremallyDisconnected_characterSpace_of_predual
    (P := WStarAlgebra.predual A) S

end StarSubalgebra

end WStarAlgebra
