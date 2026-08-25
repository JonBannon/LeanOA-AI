module

public import Mathlib.Order.ScottContinuity
public import Mathlib.Topology.Order.MonotoneConvergence

@[expose] public section

open Filter Set
open scoped Topology

variable {α β : Type*} [Preorder α] [TopologicalSpace α] [SupConvergenceClass α]
  [Preorder β] [TopologicalSpace β] [OrderClosedTopology β]

/-- A continuous monotone map out of a space in which directed suprema are topological limits is
Scott continuous. -/
theorem Continuous.scottContinuous_of_monotone {f : α → β} (hf : Continuous f)
    (hmono : Monotone f) : ScottContinuous f := by
  intro s hnon hdir a ha
  letI : Nonempty s := hnon.to_subtype
  letI : IsDirectedOrder s := ⟨hdir.directed_val⟩
  have hfa : Tendsto (fun x : s ↦ f x) atTop (𝓝 (f a)) :=
    hf.continuousAt.tendsto.comp (SupConvergenceClass.tendsto_coe_atTop_isLUB a s ha)
  simpa [Set.range_comp] using
    isLUB_of_tendsto_atTop (hmono.comp (Subtype.mono_coe (· ∈ s))) hfa
