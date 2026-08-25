module

public import LeanOA.Mathlib.Analysis.LocallyConvex.Bipolar
public import LeanOA.Mathlib.Analysis.Normed.Module.Dual
public import LeanOA.Ultraweak.Basic
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Topology.Algebra.Module.ClosedSubmodule

@[expose] public section

open scoped Ultraweak

variable {𝕜 M P : Type*} [RCLike 𝕜] [NormedAddCommGroup M] [NormedSpace 𝕜 M]
  [NormedAddCommGroup P] [NormedSpace 𝕜 P] [Predual 𝕜 M P]

variable (𝕜 M P) in
/-- The continuous dual of `M` with its ultraweak topology is its specified predual `P`. -/
noncomputable def Ultraweak.predualDualEquiv :
    P ≃ₗ[𝕜] StrongDual 𝕜 (Ultraweak 𝕜 M P) := by
  let B := topDualPairing 𝕜 P ∘ₗ
    (Predual.equivDual (M := M) |>.toLinearEquiv.toLinearMap)
  apply LinearMap.rightDualEquiv B
  intro p hp
  apply (topDualPairing_separatingRight (𝕜 := 𝕜) (E := P)) p
  intro f
  rw [← (Predual.equivDual (𝕜 := 𝕜) (M := M) (P := P)).apply_symm_apply f]
  exact hp ((Predual.equivDual (𝕜 := 𝕜) (M := M) (P := P)).symm f)

@[simp]
lemma Ultraweak.predualDualEquiv_apply_apply (p : P) (m : Ultraweak 𝕜 M P) :
    predualDualEquiv 𝕜 M P p m =
      Predual.equivDual (𝕜 := 𝕜) (M := M) (P := P) (ofUltraweak m) p := rfl

namespace Predual

/-- The canonical isometric embedding of a specified predual into the norm dual of its dual
space. -/
noncomputable def toDualₗᵢ : P →ₗᵢ[𝕜] StrongDual 𝕜 M where
  toFun p := (NormedSpace.inclusionInDoubleDual 𝕜 P p).comp
    Predual.equivDual.toContinuousLinearEquiv.toContinuousLinearMap
  map_add' p q := by ext; simp
  map_smul' c p := by ext; simp
  norm_map' p := by
    change ‖(NormedSpace.inclusionInDoubleDual 𝕜 P p).comp
      (Predual.equivDual (𝕜 := 𝕜) (M := M) (P := P)).toContinuousLinearEquiv.toContinuousLinearMap‖
        = ‖p‖
    rw [ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]
    exact (NormedSpace.inclusionInDoubleDualLi 𝕜).norm_map p

@[simp]
lemma toDualₗᵢ_apply (p : P) (x : M) :
    toDualₗᵢ (𝕜 := 𝕜) (M := M) (P := P) p x =
      Predual.equivDual (𝕜 := 𝕜) (M := M) (P := P) x p :=
  rfl

@[simp]
lemma toDualₗᵢ_apply_ofUltraweak (p : P) (x : σ(M, P)_𝕜) :
    toDualₗᵢ (𝕜 := 𝕜) (M := M) (P := P) p (ofUltraweak x) =
      Ultraweak.predualDualEquiv 𝕜 M P p x :=
  rfl

/-- The canonical image of a complete specified predual in the norm dual is closed. -/
theorem isClosed_range_toDualₗᵢ [CompleteSpace P] :
    IsClosed (Set.range (toDualₗᵢ (𝕜 := 𝕜) (M := M) (P := P))) :=
  (toDualₗᵢ (𝕜 := 𝕜) (M := M) (P := P)).isometry.isClosedEmbedding.isClosed_range

end Predual

namespace Ultraweak

variable (𝕜 M P) in
/-- The norm-closed submodule of functionals on `M` represented by its specified predual `P`.

This is the explicit, topology-free-on-the-domain realization of the continuous dual of
`\sigma(M, P)`. Keeping `P` as an argument avoids selecting a predual through a typeclass. -/
noncomputable def continuousDual [CompleteSpace P] : ClosedSubmodule 𝕜 (StrongDual 𝕜 M) where
  toSubmodule := LinearMap.range
    (Predual.toDualₗᵢ (𝕜 := 𝕜) (M := M) (P := P)).toLinearMap
  isClosed' := by
    change IsClosed (Set.range (Predual.toDualₗᵢ (𝕜 := 𝕜) (M := M) (P := P)))
    exact Predual.isClosed_range_toDualₗᵢ (𝕜 := 𝕜) (M := M) (P := P)

/-- Membership in the explicit ultraweak continuous dual is representation by an element of the
specified predual. -/
lemma mem_continuousDual [CompleteSpace P] (f : StrongDual 𝕜 M) :
    f ∈ continuousDual 𝕜 M P ↔
      ∃ p : P, Predual.toDualₗᵢ (𝕜 := 𝕜) (M := M) (P := P) p = f :=
  LinearMap.mem_range

/-- A norm-continuous functional belongs to the specified ultraweak continuous dual exactly when
it factors continuously through the explicit map to the ultraweak topology. -/
lemma mem_continuousDual_iff_exists_comp_toUltraweakL [CompleteSpace P]
    (f : StrongDual 𝕜 M) :
    f ∈ continuousDual 𝕜 M P ↔
      ∃ g : StrongDual 𝕜 (σ(M, P)_𝕜),
        g.comp (toUltraweakL 𝕜 M P) = f := by
  rw [mem_continuousDual]
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨predualDualEquiv 𝕜 M P p, ?_⟩
    ext x
    simp
  · rintro ⟨g, rfl⟩
    refine ⟨(predualDualEquiv 𝕜 M P).symm g, ?_⟩
    ext x
    rw [Predual.toDualₗᵢ_apply, ContinuousLinearMap.comp_apply, toUltraweakL_apply]
    calc
      _ = predualDualEquiv 𝕜 M P ((predualDualEquiv 𝕜 M P).symm g)
          (toUltraweak 𝕜 P x) := by
        simpa only [ofUltraweak_toUltraweak] using
          (predualDualEquiv_apply_apply ((predualDualEquiv 𝕜 M P).symm g)
            (toUltraweak 𝕜 P x)).symm
      _ = g (toUltraweak 𝕜 P x) := by rw [LinearEquiv.apply_symm_apply]

/-- Every element of the specified predual represents an ultraweakly continuous functional. -/
@[simp]
lemma Predual.toDualₗᵢ_mem_continuousDual [CompleteSpace P] (p : P) :
    Predual.toDualₗᵢ (𝕜 := 𝕜) (M := M) (P := P) p ∈ continuousDual 𝕜 M P :=
  mem_continuousDual _ |>.2 ⟨p, rfl⟩

end Ultraweak

namespace Predual

variable [CompleteSpace P]

/-- The canonical isometric embedding of a specified predual onto its image in the norm dual. -/
noncomputable def toContinuousDualₗᵢ :
    P →ₗᵢ[𝕜] (Ultraweak.continuousDual 𝕜 M P).toSubmodule where
  toFun p := ⟨toDualₗᵢ p, Ultraweak.Predual.toDualₗᵢ_mem_continuousDual p⟩
  map_add' p q := Subtype.ext <| map_add (toDualₗᵢ (𝕜 := 𝕜) (M := M) (P := P)) p q
  map_smul' c p := Subtype.ext <| map_smul (toDualₗᵢ (𝕜 := 𝕜) (M := M) (P := P)) c p
  norm_map' p := (toDualₗᵢ (𝕜 := 𝕜) (M := M) (P := P)).norm_map p

@[simp]
lemma coe_toContinuousDualₗᵢ_apply (p : P) :
    ((toContinuousDualₗᵢ p : (Ultraweak.continuousDual 𝕜 M P).toSubmodule) :
      StrongDual 𝕜 M) = toDualₗᵢ p :=
  rfl

/-- A specified Banach predual is canonically isometric to its represented submodule of the norm
dual. -/
noncomputable def continuousDualEquiv :
    P ≃ₗᵢ[𝕜] (Ultraweak.continuousDual 𝕜 M P).toSubmodule :=
  LinearIsometryEquiv.ofSurjective toContinuousDualₗᵢ fun f ↦ by
    obtain ⟨p, hp⟩ := Ultraweak.mem_continuousDual f.1 |>.1 f.2
    exact ⟨p, Subtype.ext hp⟩

@[simp]
lemma continuousDualEquiv_apply (p : P) :
    continuousDualEquiv (𝕜 := 𝕜) (M := M) (P := P) p =
      toContinuousDualₗᵢ (𝕜 := 𝕜) (M := M) (P := P) p :=
  rfl

end Predual

variable (𝕜 M P) in
/-- The explicit dual pairing between an ultraweak space and its specified predual. -/
noncomputable def Ultraweak.pairing :
    σ(M, P)_𝕜 →ₗ[𝕜] P →ₗ[𝕜] 𝕜 :=
  WeakBilin.pairing <| topDualPairing 𝕜 P ∘ₗ
    (Predual.equivDual (M := M) |>.toLinearEquiv.toLinearMap)

@[simp]
lemma Ultraweak.pairing_apply_apply (m : σ(M, P)_𝕜) (p : P) :
    pairing 𝕜 M P m p =
      Predual.equivDual (𝕜 := 𝕜) (M := M) (P := P) (ofUltraweak m) p :=
  rfl

instance Ultraweak.pairing_isWeak : (Ultraweak.pairing 𝕜 M P).IsWeak := by
  unfold Ultraweak.pairing
  infer_instance

namespace Ultraweak

/-- A normed submodule, regarded as a submodule of the corresponding ultraweak space through the
explicit canonical equivalence. -/
noncomputable def ofSubmodule (N : Submodule 𝕜 M) : Submodule 𝕜 (σ(M, P)_𝕜) :=
  N.comap (linearEquiv 𝕜 M P).toLinearMap

@[simp]
lemma mem_ofSubmodule (N : Submodule 𝕜 M) (x : σ(M, P)_𝕜) :
    x ∈ ofSubmodule (P := P) N ↔ ofUltraweak x ∈ N :=
  Iff.rfl

@[simp]
lemma ofSubmodule_iInf {ι : Sort*} (N : ι → Submodule 𝕜 M) :
    ofSubmodule (P := P) (⨅ i, N i) = ⨅ i, ofSubmodule (P := P) (N i) := by
  ext
  simp

/-- An intersection of submodules closed in the specified ultraweak topology is ultraweakly
closed. -/
theorem isClosed_iInf_ofSubmodule {ι : Sort*} (N : ι → Submodule 𝕜 M)
    (hN : ∀ i, IsClosed (ofSubmodule (P := P) (N i) : Set (σ(M, P)_𝕜))) :
    IsClosed (ofSubmodule (P := P) (⨅ i, N i) : Set (σ(M, P)_𝕜)) := by
  rw [ofSubmodule_iInf, Submodule.coe_iInf]
  exact isClosed_iInter hN

/-- The annihilator in the predual of a normed submodule of a dual space. -/
noncomputable def preannihilator (N : Submodule 𝕜 M) : Submodule 𝕜 P :=
  (pairing 𝕜 M P).polarSubmodule (ofSubmodule (P := P) N)

lemma mem_preannihilator (N : Submodule 𝕜 M) (p : P) :
    p ∈ preannihilator (P := P) N ↔
      ∀ x ∈ N, Predual.equivDual (𝕜 := 𝕜) (M := M) (P := P) x p = 0 := by
  rw [preannihilator, LinearMap.mem_polarSubmodule]
  constructor
  · exact fun h x hx ↦ by simpa using h (toUltraweak 𝕜 P x) hx
  · exact fun h x hx ↦ by simpa using h (ofUltraweak x) hx

lemma preannihilator_eq_iInf_ker (N : Submodule 𝕜 M) :
    preannihilator (P := P) N =
      ⨅ x : N, (Predual.equivDual (𝕜 := 𝕜) (M := M) (P := P) x.1).ker := by
  ext p
  simp [mem_preannihilator]

/-- The preannihilator of a submodule is norm closed. -/
theorem isClosed_preannihilator (N : Submodule 𝕜 M) :
    IsClosed (preannihilator (P := P) N : Set P) := by
  rw [preannihilator_eq_iInf_ker, Submodule.coe_iInf]
  exact isClosed_iInter fun x ↦ (Predual.equivDual (𝕜 := 𝕜) x.1).isClosed_ker

noncomputable instance (N : Submodule 𝕜 M) :
    IsClosed (preannihilator (P := P) N : Set P) :=
  isClosed_preannihilator N

theorem flip_polarSubmodule_preannihilator (N : Submodule 𝕜 M)
    (hN : IsClosed (ofSubmodule (P := P) N : Set (σ(M, P)_𝕜))) :
    (pairing 𝕜 M P).flip.polarSubmodule (preannihilator (P := P) N) =
      ofSubmodule (P := P) N := by
  simpa only [preannihilator] using
    LinearMap.flip_polarSubmodule_polarSubmodule (pairing 𝕜 M P)
      (ofSubmodule (P := P) N) hN

/-- The canonical isometric embedding of a normed submodule into the annihilator of its
preannihilator. -/
noncomputable def submoduleToAnnihilatorₗᵢ (N : Submodule 𝕜 M) :
    N →ₗᵢ[𝕜] StrongDual.polarSubmodule 𝕜 (preannihilator (P := P) N) where
  toFun x := ⟨Predual.equivDual x.1, by
    rw [StrongDual.mem_polarSubmodule]
    exact fun p hp ↦ mem_preannihilator N p |>.mp hp x.1 x.2⟩
  map_add' x y := Subtype.ext <| (Predual.equivDual (𝕜 := 𝕜)).map_add x.1 y.1
  map_smul' c x := Subtype.ext <| (Predual.equivDual (𝕜 := 𝕜)).map_smul c x.1
  norm_map' x := (Predual.equivDual (𝕜 := 𝕜)).norm_map x.1

theorem submoduleToAnnihilatorₗᵢ_surjective (N : Submodule 𝕜 M)
    (hN : IsClosed (ofSubmodule (P := P) N : Set (σ(M, P)_𝕜))) :
    Function.Surjective (submoduleToAnnihilatorₗᵢ (P := P) N) := by
  intro f
  let x := (Predual.equivDual (𝕜 := 𝕜) (M := M) (P := P)).symm f.1
  have hx : toUltraweak 𝕜 P x ∈
      (pairing 𝕜 M P).flip.polarSubmodule (preannihilator (P := P) N) := by
    rw [LinearMap.mem_polarSubmodule]
    intro p hp
    rw [LinearMap.flip_apply, pairing_apply_apply, ofUltraweak_toUltraweak]
    dsimp only [x]
    rw [
      (Predual.equivDual (𝕜 := 𝕜)).apply_symm_apply]
    exact StrongDual.mem_polarSubmodule 𝕜 _ f |>.mp f.2 p hp
  rw [flip_polarSubmodule_preannihilator N hN] at hx
  exact ⟨⟨x, mem_ofSubmodule N _ |>.mp hx⟩, Subtype.ext <|
    (Predual.equivDual (𝕜 := 𝕜)).apply_symm_apply f.1⟩

/-- An ultraweakly closed normed submodule is isometric to the annihilator of its
preannihilator. -/
noncomputable def closedSubmoduleEquivAnnihilator (N : Submodule 𝕜 M)
    (hN : IsClosed (ofSubmodule (P := P) N : Set (σ(M, P)_𝕜))) :
    N ≃ₗᵢ[𝕜] StrongDual.polarSubmodule 𝕜 (preannihilator (P := P) N) :=
  LinearIsometryEquiv.ofSurjective (submoduleToAnnihilatorₗᵢ (P := P) N)
    (submoduleToAnnihilatorₗᵢ_surjective N hN)

/-- An ultraweakly closed normed submodule is the dual of the quotient of the specified predual by
its preannihilator. -/
noncomputable def closedSubmoduleEquivDual (N : Submodule 𝕜 M)
    (hN : IsClosed (ofSubmodule (P := P) N : Set (σ(M, P)_𝕜))) :
    N ≃ₗᵢ[𝕜] StrongDual 𝕜 (P ⧸ preannihilator (P := P) N) :=
  (closedSubmoduleEquivAnnihilator N hN).trans
    (preannihilator (P := P) N).dualQuotientEquivAnnihilator.symm

/-- The quotient predual carried by an ultraweakly closed normed submodule. -/
@[implicit_reducible]
noncomputable def closedSubmodulePredual (N : Submodule 𝕜 M)
    (hN : IsClosed (ofSubmodule (P := P) N : Set (σ(M, P)_𝕜))) :
    Predual 𝕜 N (P ⧸ preannihilator (P := P) N) :=
  ⟨closedSubmoduleEquivDual N hN⟩

end Ultraweak
