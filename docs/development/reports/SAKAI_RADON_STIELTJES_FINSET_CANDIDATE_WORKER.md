# Sakai Radon--Stieltjes finite-set candidate integration report

Status: **kernel-checked conditional uniqueness; candidate semantics only**

Workstream: `rs-integration`

Baseline: coordination commit `5c33276`

Scratch file: `Scratch/SakaiRadonStieltjesFinsetCandidate.lean`

## Statement-fidelity warning

This worker does **not** claim that Sakai's notation

```text
a = ∫ λ de(λ)
```

has been proved equivalent to the finite-set limit used here.

The scratch theorem assumes explicitly that left-endpoint identity moments formed from every
finite real cut set converge ultraweakly to `a`. This is a coherent candidate semantics that makes
the preceding scratch layers compose. Certifying it as the intended translation of Sakai's source
is a separate human/source-review obligation.

Statement status: `TRANSLATED_CANDIDATE`; not `SOURCE_EQUIVALENCE_CHECKED`.

## Integrated result

The integration imports and composes exactly these existing scratch layers:

- `Scratch.FiniteCutEnumeration`;
- `Scratch.SakaiRadonStieltjesBridge`;
- `Scratch.SakaiUniquenessFinite`;
- `Scratch.CompetingSupportRecovery`.

No alternative division, spectral family, PVM, integral, support, or projection API was created.

### Concrete bridge

`tendsto_translated_and_lowerResidual_finset_Ici` instantiates the abstract bridge with:

```lean
D       := Finset ℝ
lD      := Filter.atTop
cut d   := orderedCut d
bands d := bandCount d
J       := Set.Ici c
refine  := Subtype.val
lJ      := Filter.atTop
```

The existing Mathlib identity `Filter.map_val_Ici_atTop` supplies cofinality. The endpoint escape
theorems from `FiniteCutEnumeration` supply the scalar minimum/maximum limits, and composition with
the competing family's endpoint laws supplies projection endpoint convergence.

### Source-filter-parametric theorem

The main pointwise theorem is
`competing_eq_spectralProjectionIio_of_finset_candidate`. It is intentionally more general than
bare `atTop`. Its source assumptions are:

```lean
source : Filter (Finset ℝ)
[NeBot source]
hsource : Tendsto id source atTop
```

together with the explicit candidate moment convergence, monotonicity, sequential continuity from
below, and the competing family's ultraweak endpoint laws.

This allows `source` to retain mesh, endpoint, or other cut-set-dependent admissibility conditions.
It cannot carry independent tag data without replacing `Finset ℝ` by a richer index type with a
cut-set projection. For every fixed finite cut set `c`, the map `d ↦ d ∪ c` is eventually the
identity under `hsource`; hence it tends from `source` to itself. The proof uses:

- `d ∪ {r}` for the fixed-projection split;
- `d ∪ {s,r}` for the residual-retaining lower comparison at each `s < r`.

The bare-refinement corollary is
`competing_eq_spectralProjectionIio_of_finset_atTop_candidate`.

After the independent mesh-filter experiment was integrated,
`competing_eq_spectralProjectionIio_of_mesh_refinement_candidate` instantiated the same theorem
with the checked nontrivial filter

```lean
atTop ⊓ comap divisionMesh (nhds 0).
```

This closes the Lean composition from simultaneous refinement/mesh/endpoint behavior through
pointwise recovery. It remains a candidate translation rather than a source-equivalence result.

The two-family theorem `competing_family_unique_of_finset_candidate` applies pointwise recovery to
two competing families and now permits a separate nontrivial refinement-directed source filter for
each family. `competing_family_unique_of_mesh_refinement_candidate` is the concrete specialization
when both moment limits use the checked refinement-plus-mesh filter.

## Finite mechanics discharged

The integration defines only scratch-local shims:

- `canonicalIndex d x`: the inverse `Finset.orderIsoOfFin` index when `x ∈ d`, zero otherwise;
- `belowNet`, `aboveNet`: the positive and negative finite pieces after prescribing `r`;
- `lowerNet`: the varying lower comparison after prescribing `s` and `r`.

Kernel-checked helper results show:

- `orderedCut d (canonicalIndex d x) = x` when `x ∈ d`;
- canonical indices are ordered when their cuts are ordered;
- the index of a member is at most `bandCount d`;
- `bandCount = k + (bandCount - k)` at the prescribed index;
- the abstract bridge translated sum is definitionally the finite-decomposition translated sum;
- `belowNet - aboveNet` is the complete translated moment;
- both pieces are nonnegative;
- multiplication by `e r` fixes `belowNet` and annihilates `aboveNet`;
- eventually, the finite residual lower comparison is below `belowNet`.

These facts feed directly into
`CompetingSupportRecovery.competing_eq_spectralProjectionIio_of_continuousBelow`; no separate
convergence of the positive and negative split pieces is assumed.

## Edge behavior

- Empty and singleton ambient cut sets are harmless because union with `{r}` makes the working
  division nonempty.
- A singleton working division has zero bands and places `r` at both endpoints; the finite split
  lemmas remain valid.
- For each `s < r`, `hsource` makes `{s,r} ⊆ d` eventual. On that eventual set both prescribed-cut
  unions are literally `d`, so the lower-bound comparison and the fixed `u` net agree without a
  change of source filter.
- Exact endpoint projections are never assumed at a finite stage. Only endpoint escape and the
  family-level endpoint limits are used.

## What is proved and what is not

Kernel-proved under the candidate hypotheses:

1. translated moments tend to `r • 1 - a` after prescribing `r`;
2. the finite positive/negative split satisfies the support-recovery hypotheses;
3. a competing lower family satisfies `e r = spectralProjectionIio a r` for every `r`;
4. two such competing families are equal, even when their explicit candidate moments are indexed
   by separate refinement-directed source filters;
5. the pointwise and family theorems apply to the checked nontrivial refinement-plus-mesh filter.

Not proved:

1. equivalence between Sakai's Radon--Stieltjes notation and this finite-set moment net;
2. that bare inclusion refinement alone is an analytically adequate integration filter;
3. mesh convergence, tagged-sum independence, or integral existence;
4. a production spectral-resolution structure;
5. any theorem about the source beyond the explicit candidate assumptions.

## API recommendation

Do not publish this integration theorem yet.

The order/filter design is stable and filter-parametric: retain `Finset`, inclusion refinement,
arbitrary richer source filters satisfying `Tendsto id source atTop`, and eventually-identity
finite union. The remaining review target is semantic, not proof engineering: determine whether
Sakai's integral clause really licenses this left-endpoint finite-set moment hypothesis, what
mesh/admissibility information belongs in `source`, and whether a richer tagged index is needed.

If that source review succeeds, promote a small proposition describing the moment semantics rather
than the scratch-local `canonicalIndex` or net shims. The latter should remain implementation
details unless a second theorem needs them.

## Validation

Because scratch files are not Lake library roots, their imported modules were first compiled
locally and the generated artifacts were removed before commit. The final check was:

```text
LEAN_PATH=. lake env lean Scratch/SakaiRadonStieltjesFinsetCandidate.lean
git diff --check
rg -n "\bsorry\b|\badmit\b|^axiom\b" Scratch/SakaiRadonStieltjesFinsetCandidate.lean
```

The Lean check passed without warnings or placeholders. No production file, umbrella import,
Verso source, shared coordination file, dependency, or remote was modified.
