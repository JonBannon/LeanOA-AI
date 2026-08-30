module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.Filter.AtTopBot.Finset

@[expose] public section

/-!
# Scratch: total enumeration of finite ordered cut sets

This file tests the smallest adapter from finite cut sets to the natural-number-indexed cuts used
by the existing spectral-sum API.  It deliberately keeps `Finset` as the division object and uses
Mathlib's canonical `Finset.orderEmbOfFin` for all in-range values.

The total extension is harmless on the empty set (`default`) and constant at the maximum after the
last in-range cut.  The latter convention makes a nonempty enumerator monotone on all of `ℕ`.
-/

open Filter

namespace Scratch.FiniteCutEnumeration

variable {α : Type*} [LinearOrder α] [Inhabited α]

/-- The number of adjacent bands determined by a finite set of cuts. -/
def bandCount (d : Finset α) : ℕ := d.card - 1

/-- The canonical increasing enumeration in range, extended constantly at the maximum afterward.
For the empty cut set it is the constant `default` function. -/
noncomputable def orderedCut (d : Finset α) (i : ℕ) : α :=
  if hi : i < d.card then
    d.orderEmbOfFin rfl ⟨i, hi⟩
  else if hd : d.Nonempty then d.max' hd else default

theorem orderedCut_of_lt_card (d : Finset α) {i : ℕ} (hi : i < d.card) :
    orderedCut d i = d.orderEmbOfFin rfl ⟨i, hi⟩ := by
  simp [orderedCut, hi]

theorem orderedCut_of_card_le (d : Finset α) (hd : d.Nonempty) {i : ℕ}
    (hi : d.card ≤ i) : orderedCut d i = d.max' hd := by
  simp [orderedCut, Nat.not_lt.mpr hi, hd]

@[simp]
theorem orderedCut_empty (i : ℕ) : orderedCut (∅ : Finset α) i = default := by
  simp [orderedCut]

omit [LinearOrder α] [Inhabited α] in
@[simp]
theorem bandCount_empty : bandCount (∅ : Finset α) = 0 := by
  simp [bandCount]

omit [LinearOrder α] [Inhabited α] in
@[simp]
theorem bandCount_singleton (x : α) : bandCount ({x} : Finset α) = 0 := by
  simp [bandCount]

/-- Every in-range value of the total enumerator is one of the original cuts. -/
theorem orderedCut_mem (d : Finset α) {i : ℕ} (hi : i < d.card) : orderedCut d i ∈ d := by
  rw [orderedCut_of_lt_card d hi]
  exact d.orderEmbOfFin_mem rfl ⟨i, hi⟩

/-- The zeroth cut is the minimum of every nonempty finite cut set. -/
theorem orderedCut_zero_eq_min (d : Finset α) (hd : d.Nonempty) :
    orderedCut d 0 = d.min' hd := by
  have hc : 0 < d.card := Finset.card_pos.mpr hd
  rw [orderedCut_of_lt_card d hc]
  exact Finset.orderEmbOfFin_zero rfl hc

/-- The cut at `bandCount` is the maximum of every nonempty finite cut set. -/
theorem orderedCut_bandCount_eq_max (d : Finset α) (hd : d.Nonempty) :
    orderedCut d (bandCount d) = d.max' hd := by
  have hc : 0 < d.card := Finset.card_pos.mpr hd
  have hlast : d.card - 1 < d.card := Nat.sub_lt hc Nat.zero_lt_one
  rw [bandCount, orderedCut_of_lt_card d hlast]
  exact Finset.orderEmbOfFin_last rfl hc

/-- The total extension remains monotone for every nonempty finite cut set. -/
theorem monotone_orderedCut (d : Finset α) (hd : d.Nonempty) : Monotone (orderedCut d) := by
  intro i j hij
  by_cases hj : j < d.card
  · have hi : i < d.card := lt_of_le_of_lt hij hj
    rw [orderedCut_of_lt_card d hi, orderedCut_of_lt_card d hj]
    exact (d.orderEmbOfFin rfl).monotone (by simpa using hij)
  · by_cases hi : i < d.card
    · rw [orderedCut_of_lt_card d hi,
        orderedCut_of_card_le d hd (Nat.le_of_not_gt hj)]
      exact d.le_max' _ (d.orderEmbOfFin_mem rfl ⟨i, hi⟩)
    · rw [orderedCut_of_card_le d hd (Nat.le_of_not_gt hi),
        orderedCut_of_card_le d hd (Nat.le_of_not_gt hj)]

/-- Adjacent endpoints of a genuine band are strictly ordered. -/
theorem orderedCut_lt_succ (d : Finset α) {i : ℕ} (hi : i < bandCount d) :
    orderedCut d i < orderedCut d (i + 1) := by
  change i < d.card - 1 at hi
  have hi0 : i < d.card := by
    omega
  have hi1 : i + 1 < d.card := by
    omega
  rw [orderedCut_of_lt_card d hi0, orderedCut_of_lt_card d hi1]
  exact (d.orderEmbOfFin rfl).strictMono (by simp)

/-- Every cut is recovered at an in-range index of the canonical order embedding. -/
theorem exists_index_orderedCut_eq (d : Finset α) {x : α} (hx : x ∈ d) :
    ∃ i : ℕ, ∃ _hi : i < d.card, orderedCut d i = x := by
  have hxrange : x ∈ Set.range (d.orderEmbOfFin rfl) := by
    rw [d.range_orderEmbOfFin rfl]
    exact hx
  rcases hxrange with ⟨i, rfl⟩
  exact ⟨i, i.2, orderedCut_of_lt_card d i.2⟩

/-- The left endpoint selected by the total enumerator. -/
noncomputable def leftEndpoint (d : Finset α) : α := orderedCut d 0

/-- The right endpoint selected by the total enumerator. -/
noncomputable def rightEndpoint (d : Finset α) : α := orderedCut d (bandCount d)

/-- Along refinement `atTop`, the minimum cut escapes to `atBot`. -/
theorem tendsto_leftEndpoint_atBot :
    Tendsto (leftEndpoint : Finset α → α) atTop atBot := by
  rw [tendsto_atTop_atBot]
  intro b
  refine ⟨{b}, fun d hd ↦ ?_⟩
  have hb : b ∈ d := hd (Finset.mem_singleton_self b)
  have hnonempty : d.Nonempty := ⟨b, hb⟩
  rw [leftEndpoint, orderedCut_zero_eq_min d hnonempty]
  exact d.min'_le b hb

/-- Along refinement `atTop`, the maximum cut escapes to `atTop`. -/
theorem tendsto_rightEndpoint_atTop :
    Tendsto (rightEndpoint : Finset α → α) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  refine ⟨{b}, fun d hd ↦ ?_⟩
  have hb : b ∈ d := hd (Finset.mem_singleton_self b)
  have hnonempty : d.Nonempty := ⟨b, hb⟩
  rw [rightEndpoint, orderedCut_bandCount_eq_max d hnonempty]
  exact d.le_max' b hb

end Scratch.FiniteCutEnumeration
