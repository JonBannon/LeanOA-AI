# Finite-cut enumeration worker report

Status: **kernel-checked scratch result; no production API or architecture change**

Workstream: `rs_refinement`

Baseline: coordination commit `1cd3a6552cb3866d1f7cbfc01a06c27e174355a5`

Scratch file: `Scratch/FiniteCutEnumeration.lean`

## Result

An ordered finite-cut adapter can be built directly on `Finset` and pinned Mathlib's
`Finset.orderEmbOfFin`. No division structure, sorting algorithm, index subtype, or competing
refinement relation is needed.

The kernel-tested candidate is generic over a linear order with a harmless empty-set default:

```lean
variable {α : Type*} [LinearOrder α] [Inhabited α]

def bandCount (d : Finset α) : ℕ := d.card - 1

noncomputable def orderedCut (d : Finset α) (i : ℕ) : α :=
  if hi : i < d.card then
    d.orderEmbOfFin rfl ⟨i, hi⟩
  else if hd : d.Nonempty then d.max' hd else default
```

For the spectral application, take `α := ℝ` and call the existing spectral sums with
`orderedCut d` and `bandCount d`.

The tail is constant at `d.max'` for a nonempty set. This is not source mathematics; it is a total
extension convention required only because the current spectral-sum interface accepts
`cut : ℕ → ℝ`. Every band used by the sum has both endpoints in range, so the tail is semantically
irrelevant there. The convention is useful because it makes `orderedCut d` monotone on all of
`ℕ`, rather than merely on the finite valid-index subtype.

## Existing API audit

Pinned repository/version:

```text
repository: https://github.com/leanprover-community/mathlib4.git
commit:     476ab284693e554a6b48c5f5210cb4fb5ae51252
Lean:       4.32.0-rc1, commit b4812ae53eea93439ad5dce5a5c26591c31cb697
license:    Apache-2.0
```

The decisive declarations are already in `Mathlib/Data/Finset/Sort.lean`:

| Mathlib declaration | Role |
| --- | --- |
| `Finset.orderIsoOfFin` | canonical order isomorphism from `Fin d.card` to the subtype of members of `d` |
| `Finset.orderEmbOfFin` | canonical strict increasing enumeration into `α` |
| `Finset.orderEmbOfFin_mem` | in-range enumeration values belong to `d` |
| `Finset.range_orderEmbOfFin` | every member of `d` has an in-range index |
| `Finset.orderEmbOfFin_zero` | index zero is `d.min'` when `d` is nonempty |
| `Finset.orderEmbOfFin_last` | index `d.card - 1` is `d.max'` when `d` is nonempty |

`Finset.min'_le` and `Finset.le_max'` supply the endpoint bounds. The standard
`Filter.tendsto_atTop_atBot` and `Filter.tendsto_atTop_atTop` criteria supply endpoint escape.

Sak-AI has no competing finite-cut enumerator. `LeanOA/Ultraweak/SpectralSum.lean` deliberately
uses an unbundled `cut : ℕ → ℝ` together with the first `n` adjacent intervals.
`LeanOA/Ultraweak/SpectralApproximation.lean` constructs a specific infinite dyadic cut function;
it does not solve the finite-set-to-function adaptation needed by a general Radon--Stieltjes net.

## Kernel-checked declarations

The scratch file verifies:

- `orderedCut_of_lt_card`: in-range values are definitionally the Mathlib order embedding;
- `orderedCut_of_card_le`: the nonempty out-of-range tail is the maximum;
- `orderedCut_empty`: the empty enumerator is constantly `default`;
- `bandCount_empty` and `bandCount_singleton`: empty and singleton sets have zero bands;
- `orderedCut_mem`: every in-range enumerated value belongs to the cut set;
- `exists_index_orderedCut_eq`: every member is recovered at an in-range index, using
  `Finset.range_orderEmbOfFin`;
- `orderedCut_zero_eq_min` and `orderedCut_bandCount_eq_max`: exact endpoint identification for
  nonempty cut sets;
- `monotone_orderedCut`: global monotonicity of the maximum-tailed extension for nonempty sets;
- `orderedCut_lt_succ`: strict order of the two endpoints of every valid adjacent band;
- `tendsto_leftEndpoint_atBot` and `tendsto_rightEndpoint_atTop`: endpoint escape along the
  refinement filter `atTop` on `Finset α`.

The endpoint limits need no Archimedean or topological hypothesis. For each prescribed bound `b`,
the threshold cut set `{b}` suffices: every refinement contains `b`, so its minimum is at most `b`
and its maximum is at least `b`. Consequently the statements hold in the maximally reusable
linear-order setting, including the intended specialization to `ℝ`.

## Edge semantics

| Case | Behavior |
| --- | --- |
| `d = ∅` | `bandCount d = 0`; `orderedCut d i = default`; no band is consumed |
| `d = {x}` | `bandCount d = 0`; index zero is both minimum and maximum; no band is consumed |
| `d.Nonempty`, `i < d.card` | exact `orderEmbOfFin` value, hence membership in `d` |
| `d.Nonempty`, `d.card ≤ i` | constant value `d.max'` |
| `i < bandCount d` | both `i` and `i + 1` are in range and give strictly ordered endpoints |

The empty default is intentionally not given mathematical endpoint meaning. It disappears
eventually along `atTop`, since every cut set above any singleton is nonempty.

## Public-API recommendation

1. **Do not publish a new division structure or a replacement for `Finset.orderEmbOfFin`.**
2. Keep the `orderedCut`/`bandCount` adapter local to the Radon--Stieltjes bridge at first. It is a
   representation shim from finite cut sets to Sak-AI's existing `ℕ → ℝ` spectral-sum API, not a
   new mathematical abstraction.
3. If a second production consumer needs exactly this shim, stage only a small generic helper in a
   finite-order utility file. Its public theorem surface should reuse the exact Mathlib names above
   and expose only: in-range evaluation, endpoint evaluation, membership/recovery, monotonicity,
   and valid-band adjacency.
4. Keep refinement/cofinality on the existing `Finset` inclusion order and `atTop`; this scratch
   layer composes directly with the prior prescribed-cut result and introduces no alternate order.
5. Do not encode exact finite endpoint projections here. The endpoint result is only escape of the
   scalar minimum/maximum along the refinement net. Spectral-projection endpoint normalization
   remains a separate analytic obligation.

Thus the exact current recommendation is **no new production declaration**. The bridge can use
the tested definitions privately and promote them only after actual repeated use demonstrates a
stable API boundary.

## Validation

Passed without warnings or placeholders:

```text
lake env lean Scratch/FiniteCutEnumeration.lean
git diff --check
rg -n "\bsorry\b|\badmit\b|^axiom\b" Scratch/FiniteCutEnumeration.lean
```

No production file, umbrella import, Verso source, shared coordination file, dependency, or remote
was modified.
