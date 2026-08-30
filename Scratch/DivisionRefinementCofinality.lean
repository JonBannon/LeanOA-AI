module

public import Mathlib.Order.Filter.AtTopBot.Finset
public import Mathlib.Data.Finset.Insert

@[expose] public section

/-!
# Scratch: finite-cut refinement and prescribed-cut cofinality

This file tests the smallest generic order/filter layer needed by the Radon--Stieltjes bridge.
It deliberately introduces no spectral family, integral, PVM, or public division structure.

A finite set of cuts is a `Finset α`.  The existing order is inclusion, so `d ≤ d'` means that
`d'` is the finer cut set.  The subsystem containing prescribed cuts `c` is exactly `Set.Ici c`.
-/

open Filter Set

namespace Scratch.DivisionRefinementCofinality

variable {α β : Type*}

section GenericSup

variable {γ : Type*} [SemilatticeSup γ]

/-- The order-theoretic core: adjoining one fixed element is eventually the identity along any
filter that tends to `atTop`. -/
theorem eventuallyEq_sup_const_of_tendsto_atTop (c : γ) {l : Filter γ}
    (hl : Tendsto id l atTop) :
    (fun d : γ ↦ d ⊔ c) =ᶠ[l] id := by
  filter_upwards [hl.eventually (eventually_ge_atTop c)] with d hd
  exact sup_eq_left.mpr hd

/-- Adjoining one fixed element therefore preserves and reflects every target-filter limit. -/
theorem tendsto_comp_sup_const_iff_of_tendsto_atTop (c : γ) {l : Filter γ}
    (hl : Tendsto id l atTop) {f : γ → β} {target : Filter β} :
    Tendsto (fun d ↦ f (d ⊔ c)) l target ↔ Tendsto f l target := by
  simpa [Function.comp_def] using
    tendsto_congr' ((eventuallyEq_sup_const_of_tendsto_atTop c hl).fun_comp f)

end GenericSup

namespace Finset

/-- Finite cut sets refining (that is, containing) the prescribed cuts `c`. -/
abbrev Refining (c : Finset α) := Ici c

end Finset

section FiniteCuts

variable [DecidableEq α]

/-- Finite union is a common refinement in the inclusion orientation. -/
theorem subset_union_common_refinement (d₁ d₂ : Finset α) :
    d₁ ⊆ d₁ ∪ d₂ ∧ d₂ ⊆ d₁ ∪ d₂ :=
  ⟨Finset.subset_union_left, Finset.subset_union_right⟩

/-- Adding prescribed cuts preserves all cuts of the original division. -/
theorem subset_union_prescribed (d c : Finset α) : d ⊆ d ∪ c :=
  Finset.subset_union_left

/-- Adding prescribed cuts really lands in the prescribed-cut subsystem. -/
def addPrescribedCuts (c d : Finset α) : Finset.Refining c :=
  ⟨d ∪ c, Finset.subset_union_right⟩

/-- Union is also a common refinement internal to a prescribed-cut subsystem. -/
def unionContainingCuts (c : Finset α) (d₁ d₂ : Finset.Refining c) : Finset.Refining c :=
  ⟨d₁.1 ∪ d₂.1, d₁.2.trans Finset.subset_union_left⟩

/-- The prescribed-cut subsystem is directed toward finer cut sets. -/
theorem exists_common_refinement_containingCuts (c : Finset α)
    (d₁ d₂ : Finset.Refining c) :
    ∃ d₃ : Finset.Refining c, d₁ ≤ d₃ ∧ d₂ ≤ d₃ :=
  ⟨unionContainingCuts c d₁ d₂, Finset.subset_union_left, Finset.subset_union_right⟩

@[simp]
theorem coe_addPrescribedCuts (c d : Finset α) :
    (addPrescribedCuts c d : Finset α) = d ∪ c :=
  rfl

/-- The prescribed-cut subsystem is cofinal: union supplies a containing refinement. -/
theorem exists_le_containingCuts (c d : Finset α) :
    ∃ d' : Finset.Refining c, d ≤ (d' : Finset α) :=
  ⟨addPrescribedCuts c d, Finset.subset_union_left⟩

/-- The set of divisions containing `c` is cofinal in all finite cut sets. -/
theorem isCofinal_containingCuts (c : Finset α) :
    IsCofinal (Ici c : Set (Finset α)) := by
  intro d
  exact ⟨d ∪ c, Finset.subset_union_right, Finset.subset_union_left⟩

omit [DecidableEq α] in
/-- Membership of a chosen endpoint is preserved under refinement. -/
theorem mem_of_mem_of_le {x : α} {d d' : Finset α} (hx : x ∈ d) (hdd' : d ≤ d') :
    x ∈ d' :=
  hdd' hx

omit [DecidableEq α] in
/-- In particular, designated left and right endpoints survive every refinement. -/
theorem endpoints_mem_of_le {left right : α} {d d' : Finset α}
    (hleft : left ∈ d) (hright : right ∈ d) (hdd' : d ≤ d') :
    left ∈ d' ∧ right ∈ d' :=
  ⟨hdd' hleft, hdd' hright⟩

/-- Duplicate prescribed cuts collapse automatically in a `Finset`. -/
@[simp]
theorem pair_same_eq_singleton (x : α) : ({x, x} : Finset α) = {x} := by
  simp

/-- Adding prescribed cuts is eventually the identity along any genuinely refinement-directed
filter.  Extra endpoint, mesh, or admissibility conditions may remain encoded in `l`. -/
theorem eventuallyEq_union_prescribed_of_tendsto_atTop (c : Finset α)
    {l : Filter (Finset α)} (hl : Tendsto id l atTop) :
    (fun d : Finset α ↦ d ∪ c) =ᶠ[l] id := by
  filter_upwards [hl.eventually (Filter.eventually_finset_atTop_subset c)] with d hd
  simpa using Finset.union_eq_left.mpr hd

/-- Consequently, forcing prescribed cuts preserves and reflects every target-filter limit while
leaving any extra source-filter conditions untouched. -/
theorem tendsto_union_prescribed_iff_of_tendsto_atTop (c : Finset α)
    {source : Filter (Finset α)} (hsource : Tendsto id source atTop)
    {f : Finset α → β} {target : Filter β} :
    Tendsto (fun d ↦ f (d ∪ c)) source target ↔ Tendsto f source target := by
  simpa [Function.comp_def] using
    tendsto_congr' ((eventuallyEq_union_prescribed_of_tendsto_atTop c hsource).fun_comp f)

/-- Bare `atTop` is the basic specialization of prescribed-cut invariance. -/
theorem tendsto_union_prescribed_iff (c : Finset α) {f : Finset α → β}
    {target : Filter β} :
    Tendsto (fun d ↦ f (d ∪ c)) atTop target ↔ Tendsto f atTop target :=
  tendsto_union_prescribed_iff_of_tendsto_atTop c tendsto_id

end FiniteCuts

section Filters

/-!
No local cofinal-filter theorem is needed.  Since `Finset α` is already a directed order,
`Filter.map_val_Ici_atTop` identifies the pushed-forward subsystem filter with the ambient
refinement filter, and `Filter.tendsto_comp_val_Ici_atTop` gives limit restriction as an iff.
-/

/-- Exact filter equality for restriction to divisions containing `c`. -/
theorem map_val_containingCuts_atTop (c : Finset α) :
    map ((↑) : Finset.Refining c → Finset α) atTop = atTop :=
  map_val_Ici_atTop c

/-- The subsystem `atTop` is the pullback of the ambient refinement filter. -/
theorem atTop_containingCuts_eq_comap (c : Finset α) :
    (atTop : Filter (Finset.Refining c)) =
      comap ((↑) : Finset.Refining c → Finset α) atTop :=
  atTop_Ici_eq c

/-- Restricting any net to divisions containing `c` preserves and reflects its limit. -/
theorem tendsto_comp_val_containingCuts_atTop {c : Finset α}
    {f : Finset α → β} {l : Filter β} :
    Tendsto (fun d : Finset.Refining c ↦ f d) atTop l ↔ Tendsto f atTop l :=
  tendsto_comp_val_Ici_atTop

/-- The refinement filter on the prescribed-cut subsystem is nontrivial.  Mathlib's exact map
identity proves this even though no global directed-order instance for this `Ici` subtype is used. -/
theorem neBot_atTop_refiningCuts (c : Finset α) :
    NeBot (atTop : Filter (Finset.Refining c)) := by
  apply Filter.NeBot.of_map
  rw [map_val_containingCuts_atTop]
  infer_instance

/-- Empty prescribed cuts are covered without a special case. -/
example :
    map ((↑) : Finset.Refining (∅ : Finset α) → Finset α) atTop = atTop :=
  map_val_containingCuts_atTop ∅

/-- A singleton prescribed cut is covered by the same theorem. -/
example (r : α) :
    map ((↑) : Finset.Refining ({r} : Finset α) → Finset α) atTop = atTop :=
  map_val_containingCuts_atTop {r}

section TwoCuts

variable [DecidableEq α]

/-- Two possibly equal prescribed cuts are covered by the same theorem. -/
example (s r : α) :
    Tendsto (fun d : Finset.Refining ({s, r} : Finset α) ↦ (d : Finset α)) atTop atTop :=
  (map_val_containingCuts_atTop {s, r}).le

end TwoCuts

end Filters

end Scratch.DivisionRefinementCofinality
