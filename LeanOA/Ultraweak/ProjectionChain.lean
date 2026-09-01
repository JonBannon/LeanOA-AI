module

public import LeanOA.Ultraweak.OrthogonalProjectionSum

@[expose] public section

/-!
# Orthogonal decompositions of projection chains

A nonempty chain of projections in a $W^*$-algebra admits an arbitrary orthogonal family whose
finite partial sums are dominated within the chain and whose projection supremum is the chain
supremum.  The maximal-family construction is kept private; the public theorem exposes only the
data used by order-continuity arguments.
-/

open Set

namespace IsChain

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [WStarAlgebra M]

private abbrev Projection (M : Type*) [CStarAlgebra M] :=
  {p : M // IsStarProjection p}

private def IsAdmissible (c : Set (Projection M)) (p : Projection M) : Prop :=
  p.1 ≠ 0 ∧ (∃ r ∈ c, p ≤ r) ∧ ∀ r ∈ c, Commute p.1 r.1

private def IsOrthogonalChainFamily
    (c : Set (Projection M)) (s : Set (Projection M)) : Prop :=
  (∀ p ∈ s, IsAdmissible c p) ∧ s.Pairwise fun p r ↦ p.1 * r.1 = 0

omit [StarOrderedRing M] [WStarAlgebra M] in
private theorem isOrthogonalChainFamily_empty (c : Set (Projection M)) :
    IsOrthogonalChainFamily c ∅ := by
  constructor <;> simp

omit [StarOrderedRing M] [WStarAlgebra M] in
private theorem isOrthogonalChainFamily_sUnion_of_chain (c : Set (Projection M))
    {S : Set (Set (Projection M))} (hS : ∀ s ∈ S, IsOrthogonalChainFamily c s)
    (hchain : IsChain (· ⊆ ·) S) : IsOrthogonalChainFamily c (⋃₀ S) := by
  constructor
  · intro p hp
    obtain ⟨s, hsS, hps⟩ := Set.mem_sUnion.mp hp
    exact (hS s hsS).1 p hps
  · intro p hp r hr hpr
    obtain ⟨s, hsS, hps⟩ := Set.mem_sUnion.mp hp
    obtain ⟨t, htS, hrt⟩ := Set.mem_sUnion.mp hr
    rcases eq_or_ne s t with rfl | hst
    · exact (hS s hsS).2 hps hrt hpr
    · rcases hchain hsS htS hst with hst' | hts'
      · exact (hS t htS).2 (hst' hps) hrt hpr
      · exact (hS s hsS).2 hps (hts' hrt) hpr

omit [StarOrderedRing M] [WStarAlgebra M] in
private theorem exists_maximal_isOrthogonalChainFamily (c : Set (Projection M)) :
    ∃ s : Set (Projection M), IsOrthogonalChainFamily c s ∧
      ∀ t : Set (Projection M), IsOrthogonalChainFamily c t → s ⊆ t → t = s := by
  obtain ⟨s, _, hs⟩ := zorn_subset_nonempty
    {s : Set (Projection M) | IsOrthogonalChainFamily c s}
    (fun S hSG hchain _ ↦
      ⟨⋃₀ S, isOrthogonalChainFamily_sUnion_of_chain c
        (fun s hs ↦ hSG hs) hchain, fun s hs ↦ Set.subset_sUnion_of_mem hs⟩)
    ∅ (isOrthogonalChainFamily_empty c)
  exact ⟨s, hs.prop, fun t ht hst ↦ hs.eq_of_ge ht hst⟩

omit [StarOrderedRing M] [WStarAlgebra M] in
private theorem exists_mem_chain_ge_finset
    {I : Type*} {c : Set (Projection M)} (hc : IsChain (· ≤ ·) c)
    (hcne : c.Nonempty) (p : I → Projection M)
    (hp : ∀ i, ∃ r ∈ c, p i ≤ r) (s : Finset I) :
    ∃ r ∈ c, ∀ i ∈ s, p i ≤ r := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      obtain ⟨r, hr⟩ := hcne
      exact ⟨r, hr, by simp⟩
  | @insert i s hi ih =>
      obtain ⟨r, hr, hir⟩ := hp i
      obtain ⟨t, ht, hst⟩ := ih
      rcases hc.total hr ht with hrt | htr
      · exact ⟨t, ht, by
          intro j hj
          rw [Finset.mem_insert] at hj
          rcases hj with rfl | hj
          · exact hir.trans hrt
          · exact hst j hj⟩
      · exact ⟨r, hr, by
          intro j hj
          rw [Finset.mem_insert] at hj
          rcases hj with rfl | hj
          · exact hir
          · exact (hst j hj).trans htr⟩

omit [WStarAlgebra M] in
private theorem finite_domination_of_isOrthogonalChainFamily
    {c s : Set (Projection M)} (hc : IsChain (· ≤ ·) c) (hcne : c.Nonempty)
    (hs : IsOrthogonalChainFamily c s) (t : Finset s) :
    ∃ r ∈ c,
      IsStarProjection.orthogonalFinsetSum (fun p : s ↦ p.1)
        (fun p q hpq ↦ hs.2 p.2 q.2 fun h ↦ hpq (Subtype.ext h)) t ≤ r := by
  let horth : Pairwise fun p q : s ↦ p.1.1 * q.1.1 = 0 :=
    fun p q hpq ↦ hs.2 p.2 q.2 fun h ↦ hpq (Subtype.ext h)
  obtain ⟨r, hr, htr⟩ := exists_mem_chain_ge_finset hc hcne
    (fun p : s ↦ p.1) (fun p ↦ (hs.1 p.1 p.2).2.1) t
  exact ⟨r, hr, IsStarProjection.orthogonalFinsetSum_le_of_forall_le
    (fun p : s ↦ p.1) horth htr⟩

private theorem commute_iSup_of_isOrthogonalChainFamily
    {c s : Set (Projection M)} (hs : IsOrthogonalChainFamily c s)
    {r : Projection M} (hr : r ∈ c) : Commute (⨆ p : s, p.1).1 r.1 := by
  let p : s → Projection M := fun q ↦ q.1
  let horth : Pairwise fun q t : s ↦ (p q).1 * (p t).1 = 0 :=
    fun q t hqt ↦ hs.2 q.2 t.2 fun h ↦ hqt (Subtype.ext h)
  let P := IsStarProjection.orthogonalFinsetSum p horth
  have hPmono : Monotone P := IsStarProjection.orthogonalFinsetSum_mono p horth
  apply IsStarProjection.commute_of_isLUB (WStarAlgebra.predual M)
    (Set.range P) (Set.range_nonempty P)
    (directedOn_range.mpr hPmono.directed_le)
    (IsStarProjection.isLUB_range_orthogonalFinsetSum p horth)
  rintro _ ⟨t, rfl⟩
  classical
  rw [commute_iff_eq]
  change (∑ q ∈ t, (p q).1) * r.1 = r.1 * ∑ q ∈ t, (p q).1
  rw [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun q _ ↦ (hs.1 q.1 q.2).2.2 r hr |>.eq

omit [WStarAlgebra M] in
private theorem commute_of_mem_chain
    {c : Set (Projection M)} (hc : IsChain (· ≤ ·) c)
    {p q : Projection M} (hp : p ∈ c) (hq : q ∈ c) : Commute p.1 q.1 := by
  rcases hc.total hp hq with hpq | hqp
  · exact p.2.commute_of_le q.2 hpq
  · exact (q.2.commute_of_le p.2 hqp).symm

private theorem iSup_eq_of_maximal_isOrthogonalChainFamily
    {c s : Set (Projection M)} (hc : IsChain (· ≤ ·) c)
    (hs : IsOrthogonalChainFamily c s)
    (hmax : ∀ t : Set (Projection M), IsOrthogonalChainFamily c t → s ⊆ t → t = s)
    {q : Projection M} (hcq : IsLUB c q) : (⨆ p : s, p.1) = q := by
  let p : s → Projection M := fun r ↦ r.1
  let q₀ : Projection M := ⨆ r : s, p r
  have hq₀_le_q : q₀ ≤ q := by
    apply iSup_le
    intro r
    obtain ⟨t, ht, hrt⟩ := (hs.1 r.1 r.2).2.1
    exact hrt.trans (hcq.1 ht)
  apply le_antisymm hq₀_le_q
  apply hcq.2
  intro r hr
  by_contra hrq₀
  have hq₀r : Commute q₀.1 r.1 :=
    commute_iSup_of_isOrthogonalChainFamily hs hr
  have hr_one_sub_q₀ : Commute r.1 (1 - q₀.1) :=
    (Commute.one_right r.1).sub_right hq₀r.symm
  let d : Projection M :=
    ⟨r.1 * (1 - q₀.1), r.2.mul q₀.2.one_sub hr_one_sub_q₀⟩
  have hd_le_r : d ≤ r := by
    apply d.2.le_iff_mul_eq_left r.2 |>.2
    change (r.1 * (1 - q₀.1)) * r.1 = r.1 * (1 - q₀.1)
    calc
      (r.1 * (1 - q₀.1)) * r.1 = r.1 * ((1 - q₀.1) * r.1) := mul_assoc ..
      _ = r.1 * (r.1 * (1 - q₀.1)) := by rw [hr_one_sub_q₀.eq]
      _ = (r.1 * r.1) * (1 - q₀.1) := (mul_assoc ..).symm
      _ = r.1 * (1 - q₀.1) := by rw [r.2.isIdempotentElem.eq]
  have hd_ne : d.1 ≠ 0 := by
    intro hd
    apply hrq₀
    have hle := (r.2.mul_eq_zero_iff_le_one_sub q₀.2.one_sub).mp hd
    simpa using hle
  have hd_comm (t : Projection M) (ht : t ∈ c) : Commute d.1 t.1 := by
    have hrt := commute_of_mem_chain hc hr ht
    have hq₀t : Commute q₀.1 t.1 :=
      commute_iSup_of_isOrthogonalChainFamily hs ht
    have hcomp : Commute (1 - q₀.1) t.1 :=
      (Commute.one_left t.1).sub_left hq₀t
    exact hrt.mul_left hcomp
  have hd_orth (t : s) : d.1 * (p t).1 = 0 := by
    have htq₀ : p t ≤ q₀ := le_iSup p t
    change (r.1 * (1 - q₀.1)) * (p t).1 = 0
    rw [mul_assoc, sub_mul, one_mul,
      ((p t).2.le_iff_mul_eq_right q₀.2).mp htq₀, sub_self, mul_zero]
  have hd_orth' (t : s) : (p t).1 * d.1 = 0 := by
    simpa only [star_mul, d.2.isSelfAdjoint.star_eq, (p t).2.isSelfAdjoint.star_eq,
      star_zero] using congr_arg star (hd_orth t)
  have hd_admissible : IsAdmissible c d :=
    ⟨hd_ne, ⟨r, hr, hd_le_r⟩, hd_comm⟩
  have hd_insert : IsOrthogonalChainFamily c (insert d s) := by
    constructor
    · intro t ht
      rcases Set.mem_insert_iff.mp ht with rfl | ht
      · exact hd_admissible
      · exact hs.1 t ht
    · apply hs.2.insert
      intro t ht _
      let t' : s := ⟨t, ht⟩
      exact ⟨hd_orth t', hd_orth' t'⟩
  have hd_mem : d ∈ s := by
    rw [← hmax (insert d s) hd_insert (Set.subset_insert d s)]
    exact Set.mem_insert d s
  let d' : s := ⟨d, hd_mem⟩
  exact hd_ne (d.2.isIdempotentElem.eq.symm.trans (hd_orth d'))

/-- A nonempty chain of projections has an orthogonal family whose finite partial sums are
dominated within the chain and whose supremum is the chain supremum. -/
theorem exists_orthogonal_projection_family
    {c : Set {p : M // IsStarProjection p}} (hc : IsChain (· ≤ ·) c)
    (hcne : c.Nonempty) {q : {p : M // IsStarProjection p}} (hcq : IsLUB c q) :
    ∃ s : Set {p : M // IsStarProjection p},
      ∃ horth : Pairwise fun p r : s ↦ p.1.1 * r.1.1 = 0,
        (∀ t : Finset s, ∃ r ∈ c,
          IsStarProjection.orthogonalFinsetSum (fun p : s ↦ p.1) horth t ≤ r) ∧
        (⨆ p : s, p.1) = q := by
  obtain ⟨s, hs, hmax⟩ := exists_maximal_isOrthogonalChainFamily c
  let horth : Pairwise fun p r : s ↦ p.1.1 * r.1.1 = 0 :=
    fun p r hpr ↦ hs.2 p.2 r.2 fun h ↦ hpr (Subtype.ext h)
  refine ⟨s, horth, ?_, ?_⟩
  · intro t
    simpa only [horth] using finite_domination_of_isOrthogonalChainFamily hc hcne hs t
  · exact iSup_eq_of_maximal_isOrthogonalChainFamily hc hs hmax hcq

end IsChain
