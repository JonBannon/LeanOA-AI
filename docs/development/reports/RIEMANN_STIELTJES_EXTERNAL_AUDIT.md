# External Riemann--Stieltjes infrastructure audit

## Executive finding

No audited external integral API can honestly discharge Sak-AI's missing bridge.  The available
integrals are over fixed bounded intervals and converge in a norm topology; Sakai's uniqueness
argument needs a directed system with endpoints escaping to `-∞` and `+∞`, preservation of the
strict-lower convention `e(r) = E(Iio r)`, finite prescribed cuts, and convergence in the
ultraweak topology.

The smallest useful external layer is therefore not an integral.  It is:

1. the generic filter/order API already in the pinned Mathlib (`Filter.Tendsto.comp`,
   `atTop_basis`, `eventually_ge_atTop`, and the `atTop` order on `Finset`);
2. the finite-cut design exhibited by PNT+'s `IPartition.fromPoints`/`union`; and
3. the stable, already-pinned `BoxIntegral.Prepartition.splitMany` API as a proved reference model
   for prescribed finite cuts and common refinements.

The recommended implementation is a small Sak-AI-local one-dimensional directed index whose cut
data are finite sets (common refinement by union), augmented by explicit left/right endpoint-growth
conditions.  It should use Mathlib's generic filter lemmas directly.  It should not import PNT+,
the ICERM branch, teorth/analysis, or current Mathlib's archived Riemann--Stieltjes integral.  This
keeps the existing `Iio`/`Ico` atom convention and avoids pulling a fixed-box, right-closed,
norm-topological integral into the public API.

## Audit scope and method

The audit was performed on 2026-08-30 (America/New_York).  Repositories were inspected at the
exact commits below, including source, project manifests, toolchains, license files, history, and
directly implicated pull requests.  Searches included `division`, `partition`, `prepartition`,
`tagged`, `mesh`, `refinement`, `split`, `splitMany`, `insert`, `common refinement`, `cofinal`,
`atTop`, `Riemann`, and `Stieltjes`.  The current remote heads were freshly cloned rather than
inferred from old reports.  No production Lean file, dependency, Verso file, or coordination file
was changed.

The audit distinguishes the topology and endpoint ownership actually defined by the code.  In
particular, a vector-valued norm integral is not treated as an operator-valued ultraweak integral.

## Repositories, versions, licenses, and provenance

| Repository or source | Audited revision | Lean | Mathlib | License and provenance |
|---|---|---|---|---|
| Sak-AI transaction baseline | `1cd3a6552cb3866d1f7cbfc01a06c27e174355a5` (mathematical baseline `0e5a79423227b11bf6100d0a641c4eca44057293`) | `v4.32.0-rc1` | `476ab284693e554a6b48c5f5210cb4fb5ae51252` | Repository under audit; no code copied in this workstream. |
| [PNT+](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) | `a5154676af9aa3095150ee410cdda80555aa0642` | `v4.32.2` | `905b95818eb32af7874a58b427f50c1711a5e96c` | Apache-2.0.  The relevant file records Aristotle/Harmonic and ChatGPT provenance and requests Aristotle co-authorship when reused.  It was generated against Lean `v4.24.0` and Mathlib `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`. |
| [PNT+ PR #871](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/pull/871) | head `00493819f8520e6f2fb6353549e88506b75c1e15`; merge `4d6cf4ead7b1c3097d84cb4f76efd3add29ffda6` | branch metadata evolved after the generated-file versions above | branch metadata evolved after the generated-file versions above | Apache-2.0.  The current `Unused/MyMV_A3a.lean` has SHA-256 `1b2ea2547bc796e8691807dbc27ee88344b0840007f6ffd4af02bb3f3c807158`, exactly matching the file at the merged PR head. |
| [PNT+ PR #1044](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/pull/1044) (closed, unmerged) | `02c65e2ff3634e70af78c82d6fe20304937dea6d` | `v4.28.0` | `8f9d9cff6bd728b17a24e163c9402775d9e6a365` | Apache-2.0 inherited from PNT+; an unmerged experimental branch, not an available dependency. |
| [teorth/analysis](https://github.com/teorth/analysis) | `2351317a4416aa52554f29b6adc0af63dc488eff` | `v4.29.0-rc8` | `698d2b68b870f1712040ab0c233d34372d4b56df` | Apache-2.0. |
| Sak-AI pinned [Mathlib](https://github.com/leanprover-community/mathlib4) | `476ab284693e554a6b48c5f5210cb4fb5ae51252` | `v4.32.0-rc1` | self | Apache-2.0. |
| Current [Mathlib](https://github.com/leanprover-community/mathlib4) | `3c8e222f6536ac9643441d449c4f9c872336c095` | `v4.34.0-rc2` | self | Apache-2.0.  `Archive/RiemannStieltjes.lean` entered Mathlib in commit [`3cdc35c530a0db6e3463dad8b1bbc16a7d822beb`](https://github.com/leanprover-community/mathlib4/commit/3cdc35c530a0db6e3463dad8b1bbc16a7d822beb), PR #41596. |
| [mathlib-at-ICERM26 `stieltjes` branch](https://github.com/leanprover-community/mathlib-at-ICERM26/tree/stieltjes) | `6cfe8c47ba0f477f96dffb4c71bb261c1806861a` | `v4.30.0-rc2` | self (Mathlib fork) | Apache-2.0.  This is the upstream development explicitly linked from current Mathlib's archive documentation. |
| Original [j-loreaux/LeanOA](https://github.com/j-loreaux/LeanOA) | `cb811c1006ae78a0ff1d175253200e1859843370` | `v4.32.0-rc1` | `476ab284693e554a6b48c5f5210cb4fb5ae51252` | No repository-level license file is present at this commit, and GitHub's repository-license endpoint returns 404.  No code should be copied on an assumed license. |

## Required eight-column reuse report

The classifications in the last column use the contract vocabulary exactly.

| Source | Commit | Relevant files | Relevant API | Topology | Refinement support | Prescribed cuts | Reuse decision |
|---|---|---|---|---|---|---|---|
| PNT+ finite division layer | `a5154676af9aa3095150ee410cdda80555aa0642` (identical relevant blob at PR #871 head `00493819f8520e6f2fb6353549e88506b75c1e15`) | `PrimeNumberTheoremAnd/Unused/MyMV_A3a.lean` | `RS.IPart.IPartition`, `.points`, `.mesh`, `uniformPartition`, `fromPoints`, `points_fromPoints`, `union`, `union_points`, `IsRefinement`, `union_refines_left`, `union_refines_right`, `mesh_le_of_refinement`, `exists_refinement_mesh_le` | Pure finite/order layer; endpoints are fixed real `a b`; interval intent is closed `[a,b]`. | Yes.  Refinement is reverse point-set inclusion: `IsRefinement P Q` means `Q.points ⊆ P.points`; `union` is a common refinement. | Yes on a fixed interval: `fromPoints` realizes a finite point set containing `a,b` and contained in `[a,b]`.  There is no named cut-subsystem or escaping-endpoint theorem. | **PORTABLE WITH SMALL GENERALIZATION** — strongest one-dimensional model found.  Port only the finite-set/common-refinement idea if useful, preserve the Aristotle provenance, and add asymptotic endpoints plus Sak-AI's atom convention locally.  Do not depend on the `Unused` module. |
| PNT+ tagged/integral layer | same | same | `RS.Integ.TaggedPartition`, `TaggedPartitionFilter`, `RSSum`, `HasRSIntegral`, `hasRSIntegral_iff_tendsto` | `TaggedPartitionFilter = comap mesh (nhds 0)` and target `nhds I`; real scalar, metric/norm topology; fixed `[a,b]`. | Refinement is not part of the filter.  The file can construct common refinements for estimates, but it proves no cofinal restriction to partitions containing a prescribed set. | Not at integral-filter level.  Adding cuts is not shown to preserve or induce the same filter. | **TOO SCALAR / TOO NORM-TOPOLOGICAL** — no ultraweak semantics, no endpoint escape, and no refinement-indexed convergence. |
| PNT+ Lebesgue--Stieltjes experiment (closed PR #1044) | `02c65e2ff3634e70af78c82d6fe20304937dea6d` | experimental `LebesgueStieltjes/Basic.lean` and related branch files | Thin constructions around Mathlib `StieltjesFunction.measure` | Scalar measure-theoretic Stieltjes infrastructure | No relevant division/refinement net | No | **TOO SCALAR / TOO NORM-TOPOLOGICAL** — unmerged and does not address the missing bridge. |
| teorth/analysis partition layer | `2351317a4416aa52554f29b6adc0af63dc488eff` | `Analysis/Section_11_1.lean`, `Analysis/Section_11_2.lean` | `BoundedInterval`, `Partition`, `Partition.instLE`, `Partition.instMax`, joins, piecewise-constant refinements | Set/order layer on bounded real intervals; supports `Ioo`, `Icc`, `Ioc`, and `Ico`, with endpoint ownership carried by each interval constructor. | Conceptually yes: `P ≤ P'` means `P'` is finer, and `max` is intended as intersection common refinement.  However the `Preorder` proofs and the key `le_max`/`max_le_iff` theorems contain `sorry`. | No general constructor or cofinal theorem for insertion of a finite cut set. | **USEFUL DESIGN PATTERN ONLY** — endpoint ownership is explicit, but the core refinement order is not placeholder-free and the representation has known empty-interval/noncanonical-intersection hazards. |
| teorth/analysis Chapter 11.8 Riemann--Stieltjes layer | same | `Analysis/Section_11_8.lean` plus Sections 11.1--11.2 | `α_length`, `PiecewiseConstantWith.RS_integ`, `upper_RS_integral`, `lower_RS_integral`, `RS_integ`, `RS_IntegrableOn` | Scalar real Darboux-style order construction on one fixed bounded interval; not a tagged-partition filter and not ultraweak | Uses the preceding partition relation only indirectly; no convergence along refinement | No prescribed-cut/cofinal subsystem | **TOO SCALAR / TOO NORM-TOPOLOGICAL** — it cannot express the target operator-valued ultraweak moment.  Sections 11.1, 11.2, and 11.8 contain 30, 32, and 26 `sorry`s respectively (88 total). |
| Pinned Mathlib box prepartitions | `476ab284693e554a6b48c5f5210cb4fb5ae51252` | `Mathlib/Analysis/BoxIntegral/Partition/Basic.lean`, `.../Split.lean` | `BoxIntegral.Prepartition`, `Prepartition.le_def`, `SemilatticeInf`, `IsPartition.inf`, `split`, `splitMany`, `splitMany_insert`, `splitMany_le_split`, `isPartition_splitMany`, `inf_splitMany`, `eventually_not_disjoint_imp_le_of_mem_splitMany`, `IsPartition.exists_splitMany_le` | Pure finite geometric layer, but over a fixed bounded `Box`; boxes denote `(lower, upper]` (`Ioc`) | Strong and kernel-proved.  The order has finer prepartitions below coarser ones; `inf` is common refinement.  The `Finset (ι × ℝ)` `atTop` theorem is an especially relevant cofinal-refinement pattern. | Yes: `splitMany I s` inserts every hyperplane encoded by finite `s`, on fixed `I`. | **USEFUL DESIGN PATTERN ONLY** — already available and trustworthy, but direct use would impose multidimensional fixed boxes and the opposite boundary ownership (`(q,s]` rather than Sak-AI's `[q,s) = Ico q s`).  Reuse its generic supporting lemmas, not its interval representation. |
| Pinned Mathlib abstract finite partitions | same | `Mathlib/Order/Partition/Finpartition.lean` | `Finpartition`, refinement order, `SemilatticeInf`, `bind`, `restrict`, `atomise` | Abstract lattice/order layer only | Strong common-refinement algebra | No ordered real cuts, tags, mesh, endpoint ownership, or endpoint escape | **USEFUL DESIGN PATTERN ONLY** — too abstract to supply the spectral-band index without rebuilding the missing ordered-cut semantics around it. |
| Pinned Mathlib generic filters/orders | same | `Mathlib/Order/Filter/Tendsto.lean`, `Mathlib/Order/Filter/AtTopBot/Basic.lean`, `.../Finset.lean` | `Filter.Tendsto.comp`, `tendsto_id`, `atTop_basis`, `tendsto_atTop'`, `eventually_ge_atTop`, `Monotone.tendsto_atTop_finset` | Topology-polymorphic; works with Sak-AI's specified ultraweak topology | Supplies the exact abstract language for a monotone/cofinal map and restriction of a convergent net | Finite sets ordered by inclusion make “eventually contains these cuts” immediate via `eventually_ge_atTop` | **DIRECTLY REUSABLE** — this is the stable external layer the refinement implementation should actually import and use. |
| Current Mathlib box/refinement layer | `3c8e222f6536ac9643441d449c4f9c872336c095` | same production `BoxIntegral/Partition/Basic.lean` and `.../Split.lean` | Same core APIs as the pinned revision, with routine naming evolution such as `exists_iUnion_eq_sdiff` | Same fixed-box `(lower,upper]` convention | Same strong finite refinement support | Same `splitMany` support | **USEFUL DESIGN PATTERN ONLY** — no dependency bump buys the missing asymptotic or ultraweak semantics. |
| Current Mathlib archived Riemann--Stieltjes integral | current `3c8e222...`; introduced by `3cdc35c530a0db6e3463dad8b1bbc16a7d822beb` | `Archive/RiemannStieltjes.lean` | `BoxAdditiveMap.increment`, `HasStieltjesIntegralOrdered`, `HasStieltjesIntegral`, `StieltjesIntegrable`, `stieltjesIntegral`, and Riemann specializations; continuous bilinear pairing `E → F → G` | Norm topology on normed real vector spaces, through `BoxIntegral.HasIntegral`; fixed bounded interval `(a,b]` | Delegates to BoxIntegral tagged partitions; no escaping endpoints or ultraweak specialization | Fixed-interval split machinery is available underneath, but no theorem gives Sak-AI's prescribed-cut subsystem | **TOO SCALAR / TOO NORM-TOPOLOGICAL** — it is more general than scalar-valued integration, but its convergence is still norm-topological and its endpoint convention is wrong for the lower spectral family.  It is also absent from the pinned revision. |
| ICERM Mathlib branch: stable inherited partition/filter core | `6cfe8c47ba0f477f96dffb4c71bb261c1806861a` | `Mathlib/Analysis/BoxIntegral/Partition/Basic.lean`, `Split.lean`, `Tagged.lean`, `Filter.lean`, `Onedim.lean` | `Prepartition`, `TaggedPrepartition`, `splitMany`; `IntegrationParams.toFilter`, `toFilteriUnion`, basis and nontriviality theorems; `Riemann_toFilteriUnion_eventually_iff_mesh` | Tagged-partition filters on a fixed bounded `Box`; norm-valued `HasIntegral`; `(lower,upper]` ownership | Strong fixed-box refinement and mesh-filter support | Strong `splitMany` support on fixed boxes | **USEFUL DESIGN PATTERN ONLY** — the relevant stable core is already in pinned Mathlib.  The filter shows how to combine mesh and full-partition constraints, but does not solve endpoint escape or ultraweak convergence. |
| ICERM Mathlib branch: ordered divisions | same | `Mathlib/Analysis/BoxIntegral/Partition/OrderedDivision.lean` | `OrderedDivision`, `OrderedDivision.StrictMono`, `toPrepartition`, `TaggedDivision`, conversion functions | Fixed finite real interval represented as `Ioc a b` | Intended conversion between ordered divisions and prepartitions | Division points are explicit, but there is no finite-set insertion/cofinal API comparable to PNT+'s `fromPoints`/`union` | **USEFUL DESIGN PATTERN ONLY** — branch-only and incomplete: 11 declarations in this file contain `sorry`, including partition/division conversion results. |
| ICERM Mathlib branch: Riemann--Stieltjes development | same | `Mathlib/Analysis/BoxIntegral/Stieltjes/Defs.lean`, `RiemannStieltjesSum.lean`, `Sum.lean`, `Riemann.lean`, `Basic.lean`, `IntegrationByParts.lean`, `Measure.lean` | Bilinear vector-valued `HasStieltjesIntegral`, sums, bounded-variation estimates, integration by parts, comparison with measure integration | Normed real vector spaces; fixed `(a,b]`; norm convergence | Through BoxIntegral filters, not an endpoint-growing refinement net | Only fixed-box split machinery | **TOO SCALAR / TOO NORM-TOPOLOGICAL** — branch-specific files include five further `sorry`s (four in `RiemannStieltjesSum.lean`, one in `Basic.lean`) and do not model the required ultraweak moment. |
| Mathlib scalar Stieltjes measures (pinned/current/ICERM) | revisions above | `Mathlib/MeasureTheory/Measure/Stieltjes.lean` and ICERM `BoxIntegral/Stieltjes/Measure.lean` | `StieltjesFunction`, associated measure, comparison theorems | Scalar/measure-theoretic; right-continuous convention and `Ioc` interval formulas | Measure additivity rather than the needed division net | No matching prescribed-cut convergence theorem | **TOO SCALAR / TOO NORM-TOPOLOGICAL** — useful later for scalarization, not a replacement for the operator-valued ultraweak relation. |
| Original LeanOA | `cb811c1006ae78a0ff1d175253200e1859843370` | Repository-wide search, especially `LeanOA/Ultraweak/*`, `LeanOA/CFC.lean`, `LeanOA/ComplexOrder.lean` | No Riemann--Stieltjes, ordered-division, tagged-partition, `splitMany`, or prescribed-cut API was found | Existing ultraweak/order infrastructure is already inherited by Sak-AI | No additional refinement layer | No | **USEFUL DESIGN PATTERN ONLY** — it supplies historical upstream context but no missing external component.  The absent repository license independently rules out copying on an assumed Apache basis. |

## Endpoint and order conventions that must not be conflated

- Sak-AI's lower spectral family is `e(r) = E(Iio r)`.  Its band is
  `e(s) - e(q) = E(Ico q s)`, so the cut atom belongs to the band beginning at the cut.
- Mathlib `Box` and the ICERM Stieltjes work use `Ioc q s = (q,s]`; `splitLower` owns the cut on
  the lower piece (`y ≤ x`) and `splitUpper` uses `x < y`.  Translating this structure directly
  reverses the cut ownership relevant to Sakai's scalar-atom test.
- PNT+ describes closed `[a,b]` partition points and closed tag constraints.  Its sums use adjacent
  increments, so it does not itself choose the projection-valued atom convention Sak-AI requires.
- teorth/analysis supports all four bounded-interval constructors, but its partition representation
  admits multiple constructors with the same empty set and relies on choices for intersections.

These are not cosmetic differences.  A refinement theorem that moves an atom across a cut can
prove the wrong uniqueness statement while remaining internally valid Lean.

## Placeholder and integration status

- PNT+'s audited `MyMV_A3a.lean` contains no `sorry` or `admit`, but it is outside the umbrella
  import and lives under `Unused`.  The current blob is unchanged from PR #871's head.
- teorth Sections 11.1, 11.2, and 11.8 contain 88 `sorry`s in total.  In particular, the partition
  preorder/common-refinement interface and central Chapter 11.8 results are not all kernel-proved.
- Pinned/current Mathlib's `Prepartition`, `splitMany`, abstract `Finpartition`, and generic filter
  APIs inspected here contain no placeholders.
- The ICERM branch has 16 placeholders in the directly implicated new files: 11 in
  `Partition/OrderedDivision.lean`, four in `Stieltjes/RiemannStieltjesSum.lean`, and one in
  `Stieltjes/Basic.lean`.  Its stable inherited BoxIntegral core is placeholder-free.
- Current Mathlib's archived 476-line interface is placeholder-free, but is intentionally archived
  rather than part of the production Mathlib namespace imported by Sak-AI's pinned revision.

## Smallest coherent reuse/port decision

Use directly:

- `Filter.Tendsto.comp` and the pinned `atTop` basis/eventuality API;
- `Finset` inclusion order and union for the directed prescribed-cut coordinate;
- existing Sak-AI finite band and inserted-cut lemmas, rather than reproducing their algebra in a
  generic external integral framework.

Port only as a design, if the local implementation needs a packaged division:

- PNT+'s `fromPoints`/`points_fromPoints`/`union` triangle, generalized from fixed endpoints to an
  index that also records or derives endpoint extent.  Any close code translation must retain the
  Apache-2.0 notice and the Aristotle/Harmonic attribution requested by the source.

Do not port:

- PNT+'s mesh-only `TaggedPartitionFilter` or scalar `RSSum`;
- teorth's `Partition` or Darboux Riemann--Stieltjes layer;
- ICERM's incomplete ordered-division conversions or norm-topological integral;
- current Mathlib's archived integral merely to obtain division combinatorics;
- Mathlib `Box` as Sak-AI's public one-dimensional atom representation.

The target cofinality theorem should say, in Sak-AI's own directed index, that for every finite set
of prescribed cuts there is an eventual stage containing those cuts, while both endpoints remain
free to move outward.  Restriction of a known ultraweakly convergent net to that subsystem should
then be a short application of the directly reusable generic filter API.  This is the shortest
honest route to the missing prescribed-cut/refinement bridge.

## Primary source links

- [PNT+ current source file](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/a5154676af9aa3095150ee410cdda80555aa0642/PrimeNumberTheoremAnd/Unused/MyMV_A3a.lean)
- [PNT+ merged provenance PR #871](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/pull/871)
- [PNT+ closed Lebesgue--Stieltjes PR #1044](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/pull/1044)
- [teorth Section 11.1](https://github.com/teorth/analysis/blob/2351317a4416aa52554f29b6adc0af63dc488eff/Analysis/Section_11_1.lean) and [Section 11.8](https://github.com/teorth/analysis/blob/2351317a4416aa52554f29b6adc0af63dc488eff/Analysis/Section_11_8.lean)
- [Pinned Mathlib `Prepartition.splitMany`](https://github.com/leanprover-community/mathlib4/blob/476ab284693e554a6b48c5f5210cb4fb5ae51252/Mathlib/Analysis/BoxIntegral/Partition/Split.lean)
- [Pinned Mathlib `Finpartition`](https://github.com/leanprover-community/mathlib4/blob/476ab284693e554a6b48c5f5210cb4fb5ae51252/Mathlib/Order/Partition/Finpartition.lean)
- [Current Mathlib archived Riemann--Stieltjes file](https://github.com/leanprover-community/mathlib4/blob/3c8e222f6536ac9643441d449c4f9c872336c095/Archive/RiemannStieltjes.lean)
- [ICERM Stieltjes branch](https://github.com/leanprover-community/mathlib-at-ICERM26/tree/6cfe8c47ba0f477f96dffb4c71bb261c1806861a/Mathlib/Analysis/BoxIntegral)
- [Original LeanOA audited commit](https://github.com/j-loreaux/LeanOA/tree/cb811c1006ae78a0ff1d175253200e1859843370)
