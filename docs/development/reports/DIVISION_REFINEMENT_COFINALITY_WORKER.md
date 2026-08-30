# Finite-cut refinement and prescribed-cut cofinality worker report

Status: **kernel-checked scratch result; no production API or architecture change**

Workstream: `rs_refinement`

Baseline: coordination commit `1cd3a6552cb3866d1f7cbfc01a06c27e174355a5`

Scratch file: `Scratch/DivisionRefinementCofinality.lean`

## Result

The finite-cut/refinement layer needed for prescribed-cut insertion does not require a new
division structure or a custom cofinality filter.

The smallest candidate is:

```lean
division index     := Finset α
refinement order   := d ≤ d'       -- definitionally `d ⊆ d'`
prescribed system  := Set.Ici c  -- `{d : Finset α // c ⊆ d}`
common refinement  := d₁ ∪ d₂
insert cuts        := d ∪ c
refinement filter  := Filter.atTop
```

Thus larger elements are finer divisions. This orientation is deliberate: refinement proceeds
toward `atTop`.

For the immediate Sakai application, specialize `α := ℝ`. None of the cofinality or filter
arguments uses the linear order on `ℝ`; scalar order is needed only later to sort cuts and form
adjacent bands.

## Existing Sak-AI audit

Sak-AI currently has no generic finite-division/refinement object to reuse.

- `LeanOA/Ultraweak/SpectralSum.lean` uses unbundled finite prefixes of functions
  `cut : ℕ → ℝ`.
- `LeanOA/Ultraweak/SpectralApproximation.lean` works with arbitrary filtered families of those
  unbundled cuts and supplies the concrete equality `dyadicSpectralCut_refines`; it does not
  define a general refinement relation or prescribed-cut filter.
- The prior uniqueness scratch file has a positional `insertCut` for a chosen monotone sequence.
  This proves the finite band algebra, but it is not a division-independent cofinality API.
- Searches of the read-only original LeanOA checkout found no competing division, refinement, or
  prescribed-cut infrastructure.

Consequently this worker did not duplicate an existing Sak-AI object.

## Pinned Mathlib audit

Audited repository and version:

```text
repository: https://github.com/leanprover-community/mathlib4.git
commit:     476ab284693e554a6b48c5f5210cb4fb5ae51252
Lean:       4.32.0-rc1, commit b4812ae53eea93439ad5dce5a5c26591c31cb697
license:    Apache-2.0
```

The decisive existing declarations are:

| File | Declaration/API | Use here |
| --- | --- | --- |
| `Mathlib/Data/Finset/Lattice/Basic.lean` | inclusion order, `∪` as supremum, `subset_union_left`, `subset_union_right` | refinement and common refinement |
| `Mathlib/Data/Finset/Basic.lean` | `Finset.isDirected_le` | ambient finite cuts are directed |
| `Mathlib/Order/Filter/AtTopBot/Finset.lean` | `Filter.atTop_finset_eq_iInf`, `eventually_finset_atTop_subset`, `eventually_finset_mem_atTop` | every fixed finite set of cuts is eventually present |
| `Mathlib/Order/Filter/AtTopBot/Basic.lean` | `map_val_atTop_of_Ici_subset`, `map_val_Ici_atTop`, `atTop_Ici_eq`, `tendsto_comp_val_Ici_atTop` | exact cofinal-subsystem filter equality and limit restriction |
| `Mathlib/Order/Filter/AtTopBot/Tendsto.lean` | `Monotone.tendsto_atTop_atTop` | generic monotone/cofinal-map fallback; not needed for the final subtype proof |
| `Mathlib/Order/Bounds/Basic.lean` | `IsCofinal`, `IsCofinalFor` API | proposition-level cofinality vocabulary |

In particular, pinned Mathlib already proves the exact identities

```lean
Filter.map_val_Ici_atTop c
  : map ((↑) : Set.Ici c → Finset α) atTop = atTop

Filter.atTop_Ici_eq c
  : atTop = comap ((↑) : Set.Ici c → Finset α) atTop

Filter.tendsto_comp_val_Ici_atTop
  : Tendsto (fun d : Set.Ici c ↦ f d) atTop target ↔
      Tendsto f atTop target
```

The last statement is generic in the target filter. It is stronger than the one-way
topological-limit theorem requested by this transaction.

`Mathlib.Order.Partition.Partition` and `Finpartition` were also inspected. They concern
partitions of a fixed complete-lattice element, use a different refinement orientation, and do
not supply ordered real cuts, endpoint escape, or the required moment-sum indexing. They would be
an unnecessarily indirect representation here.

## Kernel-checked scratch declarations

The scratch file checks the following finite mechanics:

- `Finset.Refining c := Set.Ici c` (scratch namespace only);
- `subset_union_common_refinement`;
- `addPrescribedCuts` and `subset_union_prescribed`;
- `unionContainingCuts` and `exists_common_refinement_containingCuts`;
- `exists_le_containingCuts` and `isCofinal_containingCuts`;
- `mem_of_mem_of_le` and `endpoints_mem_of_le`;
- `pair_same_eq_singleton`.

It then checks the exact filter interface:

- `map_val_containingCuts_atTop`;
- `atTop_containingCuts_eq_comap`;
- `tendsto_comp_val_containingCuts_atTop`;
- `neBot_atTop_refiningCuts`.

These are scratch wrappers around existing Mathlib theorems, not publication proposals.

## General-filter insertion theorem

The useful additional observation is that endpoint or admissibility semantics need not be thrown
away by choosing bare `atTop` as the entire source filter.

For any `source : Filter (Finset α)` satisfying

```lean
Tendsto id source atTop,
```

every fixed finite `c` is eventually contained in the current cut set. Therefore

```lean
(fun d ↦ d ∪ c) =ᶠ[source] id
```

and hence, for every `f` and every target filter,

```lean
Tendsto (fun d ↦ f (d ∪ c)) source target ↔
  Tendsto f source target.
```

The kernel-checked names are
`eventuallyEq_union_prescribed_of_tendsto_atTop` and
`tendsto_union_prescribed_iff_of_tendsto_atTop`.

This matters for source fidelity: a later Radon--Stieltjes bridge may encode endpoint escape,
mesh, tags, or admissibility in a filter finer than the bare refinement filter. As long as its cut
projection tends to `atTop`, insertion of fixed cuts is eventually literally the identity, so all
such conditions and every established limit survive unchanged.

The proof is not specifically about finsets. The scratch file also kernel-checks the absent but
natural order-theoretic form:

```lean
variable [SemilatticeSup γ]

eventuallyEq_sup_const_of_tendsto_atTop (c : γ)
    (hl : Tendsto id source atTop) :
    (fun d ↦ d ⊔ c) =ᶠ[source] id
```

and the corresponding generic `Tendsto` iff. A search of pinned Mathlib found the ingredients but
not this assembled eventual-equality lemma.

## Required stress tests

| Test | Result |
| --- | --- |
| Empty prescribed set | `Set.Ici (∅ : Finset α)` has the same pushed-forward `atTop` filter |
| Singleton | the same `map_val_Ici_atTop` theorem applies to `{r}` |
| Duplicate cuts | `{r,r} = {r}` by `Finset` extensionality/simplification |
| Endpoint preservation | membership is monotone under refinement; more strongly, union insertion is eventually the identity, so asymptotic endpoint data is eventually unchanged |
| Finite unions | `d₁ ∪ d₂` is a common refinement |
| Prescribed subsystem directedness | union remains inside `Set.Ici c` and bounds both inputs |
| Order orientation | `d ≤ d'` means `d ⊆ d'`, hence `d'` is finer and refinement runs toward `atTop` |
| Nontriviality | derived from `map_val_Ici_atTop` and ambient `atTop.NeBot` |
| `map`/`comap` | exact equalities are existing Mathlib theorems, not merely inequalities |
| Generic limit restriction | existing `tendsto_comp_val_Ici_atTop` is an iff for an arbitrary target filter |

## Endpoint boundary

This result does **not** assume exact finite endpoint projections and does not turn endpoint limits
into exact endpoint values. It only establishes that inserting a fixed finite set cannot disturb
an endpoint or mesh condition eventually.

The Radon--Stieltjes bridge still has to define the moment approximant, state the actual asymptotic
endpoint conditions, and prove that its source filter tends to the refinement `atTop`. This worker
has not proved moment convergence, endpoint convergence, sorting/adjacency, or source equivalence.

## Public-API recommendation

1. **Do not publish a `FiniteDivision`, refinement filter, cofinal-map theorem, or spectral
   wrapper.** `Finset`, `Set.Ici`, and the pinned Mathlib filter theorems already supply them.
2. In the source bridge, use `Set.Ici c` directly unless repeated signatures demonstrate that a
   transparent local abbreviation such as `Finset.Refining c` materially improves readability.
3. Use `Filter.tendsto_comp_val_Ici_atTop` directly for bare-`atTop` restriction.
4. If the source bridge genuinely needs insertion inside a richer filter, consider staging only
   the general semilattice eventual-equality lemma above in the mirrored Mathlib hierarchy. Do not
   publish both generic and finset-specific wrappers; the `Tendsto` corollary is one line via
   `tendsto_congr'`.

Thus the current worker recommendation is **no production declaration yet**. The missing
mathematics is now clearly in the moment/endpoint representation layer, not finite-cut
cofinality.

## Validation

Passed without warnings or placeholders:

```text
lake env lean Scratch/DivisionRefinementCofinality.lean
git diff --check
rg -n "\bsorry\b|\badmit\b|^axiom\b" Scratch/DivisionRefinementCofinality.lean
```

No production file, umbrella import, Verso source, shared coordination file, dependency, or remote
was modified.
