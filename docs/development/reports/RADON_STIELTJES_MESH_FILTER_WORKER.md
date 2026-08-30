# Radon--Stieltjes mesh-filter worker report

Status: **complete kernel-checked candidate; source equivalence deliberately unclaimed; no
production API**

Workstream: `rs_mesh_filter`

Baseline: `8642b25ec879a4ab02a3c7b534e5d7fd5902a985`

Scratch file: `Scratch/RadonStieltjesMeshFilter.lean`

## Result

The concrete richer filter requested by the refinement audit is simultaneously feasible:

```lean
stieltjesFilter =
  (atTop : Filter (Finset ℝ)) ⊓ comap divisionMesh (nhds 0)
```

Here `divisionMesh d` is the maximum length of the canonically enumerated adjacent bands of `d`,
with value zero when `d` has no bands.  The scratch proves, without assumptions or placeholders,

```lean
NeBot stieltjesFilter
Tendsto id stieltjesFilter atTop
Tendsto divisionMesh stieltjesFilter (nhds 0)
Tendsto leftEndpoint stieltjesFilter atBot
Tendsto rightEndpoint stieltjesFilter atTop.
```

It also proves that adjoining any fixed finite prescribed set is eventually literally the
identity, and hence preserves and reflects convergence to every target filter.

This demonstrates that refinement, endpoint escape, and mesh convergence are compatible.  It
does **not** demonstrate that this filter is Sakai's abstract Radon--Stieltjes semantics.

## Hard compatibility gate

For every finite `S`, real `R`, and `ε > 0`, the file constructs one finite `d` satisfying

```text
S ⊆ d,
leftEndpoint d ≤ -R,
R ≤ rightEndpoint d,
divisionMesh d < ε.
```

The construction is not an added hypothesis.  It takes the compact interval spanned by the
prescribed cuts and zero, obtains a finite `ε / 4`-net from Mathlib's total-boundedness theorem,
and adjoins that net to the prescribed cuts.  If an adjacent gap in the resulting cut set were at
least `ε / 2`, its midpoint would have a net point strictly inside the gap, contradicting
canonical adjacency.  This yields a refinement of arbitrarily small mesh.  Adding the two cuts
`-R` and `R` gives the explicit two-sided endpoint witness.

The `NeBot` proof then uses the exact bases of `atTop` and the metric neighborhood filter.  Thus it
checks the simultaneous feasibility of the two coordinates of the infimum filter rather than
inferring nontriviality from the coordinates separately.

## Kernel-checked declarations

- `adjacentGaps`, `divisionMesh`;
- `divisionMesh_nonneg`, `adjacent_gap_le_divisionMesh`, `divisionMesh_le`;
- `no_mem_Ioo_orderedCut_succ`;
- `exists_refinement_divisionMesh_lt`;
- `exists_refinement_endpoints_divisionMesh_lt`;
- `stieltjesFilter`, `stieltjesFilter_neBot`;
- `tendsto_id_stieltjesFilter_atTop`;
- `tendsto_divisionMesh_stieltjesFilter`;
- `tendsto_leftEndpoint_stieltjesFilter`;
- `tendsto_rightEndpoint_stieltjesFilter`;
- `eventuallyEq_union_prescribed`;
- `tendsto_union_prescribed_iff`.

The file reuses `Scratch.FiniteCutEnumeration` for sorting and endpoints and
`Scratch.DivisionRefinementCofinality` for prescribed-cut invariance.  It introduces no competing
division order or endpoint convention.

## Mathlib reuse and provenance

Pinned environment:

```text
Mathlib repository: https://github.com/leanprover-community/mathlib4.git
Mathlib commit:     476ab284693e554a6b48c5f5210cb4fb5ae51252
Mathlib license:    Apache-2.0
Lean:               v4.32.0-rc1
Lean commit:        b4812ae53eea93439ad5dce5a5c26591c31cb697
```

The construction directly reuses:

- `totallyBounded_Icc` / `Metric.finite_approx_of_totallyBounded` for the finite net;
- `Finset.orderEmbOfFin`, through the existing enumeration scratch, for strict adjacent cuts;
- `Filter.atTop_basis`, `Metric.nhds_basis_ball`, `Filter.HasBasis.comap`, and
  `Filter.HasBasis.inf_basis_neBot_iff` for the nontriviality proof;
- the existing generic prescribed-union theorem from the cofinality scratch.

The external PNT+ partition development was consulted as a design comparison in the preceding
audit, but no PNT+ definition or proof text was copied into this scratch.  No dependency or
license obligation was added.

## Source-fidelity boundary and recommendation

This is a mathematically coherent **candidate** for the finite-cut refinement/mesh coordinate.  A
bare `Finset ℝ` `atTop` filter was already known to support prescribed-cut cofinality and endpoint
escape; this transaction adds the essential small-mesh condition without making the filter
trivial.

It remains unproved that Sakai's phrase "abstract Radon--Stieltjes integral" is equivalent to
convergence of left-endpoint sums along this exact filter.  In particular, a source-faithful
definition may require tagged partitions, a fixed finite interval followed by endpoint limits, or
another division presentation.  Therefore:

1. keep this file scratch-only;
2. use it to instantiate the already checked generic moment/endpoint bridge for experiments;
3. do not mark Sakai 1.11.3 complete until a source-equivalence or appropriately cited semantics
   theorem connects the abstract integral to the chosen finite sums.

## Validation

Run in `/private/tmp/sakai-rs-mesh-filter-8642b25` on branch `agent/rs-mesh-filter`:

```text
lake env lean Scratch/RadonStieltjesMeshFilter.lean
git diff --check
rg -n "\bsorry\b|\badmit\b|^axiom\b" Scratch/RadonStieltjesMeshFilter.lean
```

The focused Lean command passed with no output, warnings, placeholders, or added axioms.  No
production source, umbrella import, Verso source, shared coordination file, dependency pin, or
remote was modified.
