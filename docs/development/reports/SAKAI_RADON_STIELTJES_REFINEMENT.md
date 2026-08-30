# Sakai 1.11.3: Radon--Stieltjes refinement bridge

Status: **substantial kernel-checked infrastructure; source semantics still OPEN; Sakai 1.11.3
NOT YET FORMALIZED**

This report integrates the external audit, finite-cut/refinement work, finite-cut enumeration, and
the abstract ultraweak moment/endpoint bridge.  It deliberately does not turn a convenient
`Finset ℝ` model into Sakai's definition by assertion.

## A. Baseline and evidence

The transaction began from:

```text
repository: /Users/jonbannon/LeanRepos/LeanOA-AI
branch:     master
source mathematical HEAD: 0e5a79423227b11bf6100d0a641c4eca44057293
coordination HEAD:          1cd3a6552cb3866d1f7cbfc01a06c27e174355a5
Lean:                       v4.32.0-rc1
Mathlib:                    476ab284693e554a6b48c5f5210cb4fb5ae51252
```

The conclusions below are supported by these isolated or integrated evidence commits:

| Work | Commit | Evidence |
|---|---|---|
| External audit | `9db229596a238103db779e0435cb563573b107dc` | `RIEMANN_STIELTJES_EXTERNAL_AUDIT.md`; exact source/version/license/provenance audit and source-equivalence boundary |
| Finite cuts and `Ici` cofinality | `948b7c447ca8d62b69ec0c1e21da3d3b0757ca94` | `Scratch/DivisionRefinementCofinality.lean`; generic and `Finset` cofinal restriction |
| Sorted finite-cut adapter and endpoints | `f7bd0bdfe56cbbce4f84dd07389167270f97892c` | `Scratch/FiniteCutEnumeration.lean`; canonical enumeration and endpoint escape |
| Abstract moment/endpoint bridge | `9b657eed60d0f9e2b7766ad4ec21dfba64a55530` | `Scratch/SakaiRadonStieltjesBridge.lean`; finite translation identity and generic ultraweak cofinal bridge |
| Source/finite split | `6e349da6425e77fc20e439bd4e0d2cfefded9ef7` | finite inserted-cut algebra, positivity, localization, and residual lower bound |
| Conditional support recovery | `b25d751b0d838d753d195704ca5270f7a0cb0204` | support recovery and uniqueness under explicit approximation hypotheses |
| Production fixed-projection layer | `979f14da3bc1d8f45ba8c12e8dbc6c606170ecb1` | reusable ultraweak decomposition and support infrastructure |

No initial build was rerun merely to write this report.  The focused worker validations are
recorded in Section P; integration-wide validation remains a lead-integration gate.

## B. External Riemann--Stieltjes audit

The full exact eight-column audit is in
`docs/development/reports/RIEMANN_STIELTJES_EXTERNAL_AUDIT.md`.  Its operational conclusions are:

- PNT+ has the closest one-dimensional finite-point implementation:
  `IPartition.fromPoints`, `points_fromPoints`, `union`, `union_refines_left`, and
  `union_refines_right`.  This is **PORTABLE WITH SMALL GENERALIZATION**, but the file is under
  `Unused`, is absent from the umbrella import, and carries explicit Aristotle/Harmonic
  attribution requirements.  Its integral filter is `comap mesh (nhds 0)`, scalar, fixed-interval,
  and **TOO SCALAR / TOO NORM-TOPOLOGICAL** for Sakai.
- teorth/analysis Sections 11.1, 11.2, and 11.8 provide useful interval-ownership ideas, but the
  relevant three files contain 88 `sorry`s.  Chapter 11.8 is a scalar Darboux construction, not an
  ultraweak refinement net.
- pinned Mathlib already contains the proved finite-cut pattern
  `BoxIntegral.Prepartition.splitMany`, common refinement by `inf`, and finite-cut `atTop`
  arguments.  Its fixed boxes use `(q,s]`, opposite Sak-AI's `[q,s)` band ownership, so it is a
  design reference rather than Sak-AI's division representation.
- current Mathlib's `Archive/RiemannStieltjes.lean` and the fuller ICERM branch are fixed-box,
  norm-topological developments.  The archive is also absent from pinned Mathlib.  The ICERM-only
  ordered-division/Stieltjes files contain 16 directly relevant placeholders.
- original LeanOA contains no additional division, prescribed-cut, or Riemann--Stieltjes layer.
- pinned Mathlib's generic filter/order facts are **DIRECTLY REUSABLE**.  No external code was
  copied, no dependency was added, and no Mathlib update is warranted.

## C. Candidate division/refinement architecture

For the combinatorial prescribed-cut coordinate, the checked candidate is:

```text
cut set:             Finset ℝ
refinement:          d ≤ d'  definitionally means  d ⊆ d'
common refinement:  d₁ ∪ d₂
prescribed system:  Set.Ici S = {d // S ⊆ d}
refinement filter:  Filter.atTop
```

This orientation makes larger cut sets finer.  Directedness is inherited from the `Finset`
semilattice; union bounds both inputs.  The scratch theorems
`subset_union_common_refinement`, `unionContainingCuts`, and
`exists_common_refinement_containingCuts` verify the concrete mechanics.

No new `Division`, refinement relation, or cofinal filter should be published.  Mathlib already
supplies the order and filter structures.  The linear order on `ℝ` enters only when cuts are
enumerated to feed the existing `cut : ℕ → ℝ` spectral-sum API.

The checked private adapter is:

```text
bandCount d = d.card - 1
orderedCut d : ℕ → ℝ
```

where in-range values use `Finset.orderEmbOfFin` and the out-of-range tail is the maximum for a
nonempty set.  The scratch proves membership, recovery of every cut, global monotonicity for
nonempty sets, strict order of each valid adjacent pair, and exact minimum/maximum endpoint
identification.  This is a representation shim, not a new foundational object.

## D. Prescribed cuts and cofinality

For a fixed finite `S`, insertion is union:

```text
insertCuts d S = d ∪ S.
```

The checked facts include:

```text
d ⊆ d ∪ S
S ⊆ d ∪ S
IsCofinal (Set.Ici S : Set (Finset ℝ))
```

More decisively, pinned Mathlib already proves the exact subsystem identities:

```lean
Filter.map_val_Ici_atTop S
  : map ((↑) : Set.Ici S → Finset ℝ) atTop = atTop

Filter.atTop_Ici_eq S
  : (atTop : Filter (Set.Ici S)) =
      comap ((↑) : Set.Ici S → Finset ℝ) atTop

Filter.tendsto_comp_val_Ici_atTop
  : Tendsto (fun d : Set.Ici S ↦ f d) atTop target ↔
      Tendsto f atTop target
```

Thus Mathlib's `Ici` theorem—not a custom spectral lemma—is the exact bare-`atTop` cofinality and
limit-restriction result.

The scratch also checks the more useful richer-filter observation.  For any
`source : Filter (Finset ℝ)` satisfying

```lean
Tendsto id source atTop,
```

union with `S` is eventually literally the identity.  Therefore it preserves and reflects every
target-filter limit:

```lean
Tendsto (fun d ↦ f (d ∪ S)) source target ↔ Tendsto f source target.
```

The checked names are `eventuallyEq_union_prescribed_of_tendsto_atTop` and
`tendsto_union_prescribed_iff_of_tendsto_atTop`; a semilattice-sup version is checked as well.
This is the form a future source-faithful mesh/endpoint filter should consume.

## E. Sakai's source formulation and the exact conditional Lean bridge

In Theorem 1.11.3, printed pages 26--27, Sakai requires:

1. an increasing real-indexed projection family `e`;
2. one-sided increasing ultraweak continuity;
3. limits `e(t) → 0` at `-∞` and `e(t) → 1` at `+∞`; and
4. `a = ∫ λ de(λ)` as an abstract Radon--Stieltjes integral in `σ(M,M_*)`.

For existence he uses finite divisions with adjacent gaps below `ε` and lets `ε → 0`.  For
uniqueness he splits the abstract integral at an arbitrary `r`.  He does not give a Moore--Smith
index type, an order on divisions, a tag convention, or a cofinal-refinement proof.

The checked scratch fixes the finite left-endpoint convention:

```lean
identityMomentSum e cut n =
  ∑ i ∈ range n, cut i • (e (cut (i + 1)) - e (cut i))

translatedMomentSum e r cut n =
  ∑ i ∈ range n, (r - cut i) • (e (cut (i + 1)) - e (cut i)).
```

It proves without topology or endpoint normalization:

```text
translatedMomentSum
  = r • (e(right) - e(left)) - identityMomentSum.
```

The exact kernel-checked analytic signature then keeps the source division data abstract:

```lean
lD : Filter D
lJ : Filter J
cut : D → ℕ → ℝ
bands : D → ℕ
refine : J → D
hrefine : Tendsto refine lJ lD

hmoment : Tendsto
  (fun d ↦ toUltraweak ℂ P (identityMomentSum e (cut d) (bands d))) lD
  (nhds (toUltraweak ℂ P a))

hcutLeft  : Tendsto (fun d ↦ cut d 0) lD atBot
hcutRight : Tendsto (fun d ↦ cut d (bands d)) lD atTop
heAtBot   : Tendsto (fun t ↦ toUltraweak ℂ P (e t)) atBot
  (nhds (toUltraweak ℂ P 0))
heAtTop   : Tendsto (fun t ↦ toUltraweak ℂ P (e t)) atTop
  (nhds (toUltraweak ℂ P 1)).
```

`tendsto_translated_and_lowerResidual_of_cofinal_of_endpoint_escape` derives along `lJ`:

```text
translatedMomentSum e r → r • 1 - a

(r-s)e(s) - (r-s)e(left_endpoint) → (r-s)e(s).
```

This is a genuine theorem for arbitrary source and prescribed-subsystem filters.  It is not yet a
definition of Sakai's abstract integral: `hmoment` remains the explicit representation input.

## F. Limit restriction

There are now two checked levels.

1. For bare finite-cut `atTop`, `Filter.tendsto_comp_val_Ici_atTop` says restriction to cut sets
   containing `{r}` or `{s,r}` preserves and reflects every limit, including an ultraweak one.
2. For any richer filter on finite cut sets whose identity map tends to refinement `atTop`, union
   with fixed prescribed cuts is eventually equal to the identity.  Hence it preserves the moment,
   endpoint, mesh, tag, or admissibility limits already encoded in that filter.

The abstract bridge needs only `hrefine : Tendsto refine lJ lD`, so it is compatible with either
route.  Gate 5 is therefore proved generically, conditional on an actual source filter and cofinal
map being supplied.

## G. Endpoint treatment

No checked theorem assumes `e(left) = 0` or `e(right) = 1` at a finite stage.

For the concrete bare-`Finset` candidate,
`tendsto_leftEndpoint_atBot` and `tendsto_rightEndpoint_atTop` prove that the minimum and maximum
cut escape along `atTop`.  Composing these with Sakai's family-level endpoint limits gives the
needed projection limits.  More generally, the bridge takes endpoint escape and family endpoint
limits as separate hypotheses.

The finite lower comparison retains the honest residual:

```text
(r-s)e(s) - (r-s)e(left_endpoint) ≤ belowSum.
```

Only its ultraweak limit removes the residual.  This exactly avoids the stronger and
source-incorrect assumption of finite endpoint normalization.

## H. Interface with the checked support recovery

Once a source-certified filter supplies `hmoment`, endpoint escape, and prescribed-cut
cofinality, the remaining intended composition is:

```text
source identity moments and endpoints
  → cofinal subsystem containing s and r
  → translated total and residual limits
  → existing finite below/above split and localization
  → production ProjectionDecomposition
  → both checked support inequalities
  → continuity from below
  → e(r) = spectralProjectionIio a r
  → family extensionality.
```

The enumeration scratch also proves that every prescribed cut has an in-range index.  The small
positional lemma placing the index of `s` before that of `r` when `s < r`, and adapting the total
`bandCount` to the finite split signature, has not been assembled with the support scratch as one
theorem.  This is routine finite engineering, but it is not reported as checked.

The conditional support theorem remains scratch-only.  Its source hypotheses have not yet been
discharged, so it must not be promoted merely because the abstract transport theorem now exists.

## I. Sakai Theorem 1.11.3

```text
NOT YET FORMALIZED
```

The remaining blocker is precise and lies before the support argument: no source-reviewed Lean
filter/predicate has yet been shown to mean Sakai's phrase “abstract Radon--Stieltjes integral with
respect to the `σ(M,M_*)` topology.”

In particular, bare `Finset ℝ` atTop is **not** source-equivalent merely because it solves
prescribed cuts.  It forces every fixed finite cut set to appear eventually and makes the extrema
escape, but it does not make the maximum adjacent gap tend to zero.  After any threshold `S`, one
may refine to `S ∪ {R}` with `R` arbitrarily far above `max S`, producing an arbitrarily large final
gap.  Conversely, requiring convergence over every such superset may be stronger than Sakai's
small-mesh division language.  This mismatch must not be hidden.

### Exact next missing statement

The next bounded transaction should scratch-define a richer filter

```lean
sakaiDivisionFilter : Filter (Finset ℝ)
```

with a reviewed basis of the following mathematical form:

```text
parameters: prescribed cuts S, range R≥0, tolerance ε>0
basis set:  {d |
  S ⊆ d
  and leftEndpoint d ≤ -R
  and R ≤ rightEndpoint d
  and divisionMesh d ≤ ε}
```

and kernel-prove at least:

```lean
Filter.NeBot sakaiDivisionFilter
Tendsto id sakaiDivisionFilter atTop
Tendsto leftEndpoint sakaiDivisionFilter atBot
Tendsto rightEndpoint sakaiDivisionFilter atTop
Tendsto divisionMesh sakaiDivisionFilter (nhds 0).
```

The exact source-facing statement to certify is then:

```lean
HasSakaiRadonStieltjesRepresentation e a ↔
  Tendsto
    (fun d ↦ toUltraweak ℂ P
      (identityMomentSum e (orderedCut d) (bandCount d)))
    sakaiDivisionFilter
    (nhds (toUltraweak ℂ P a)).
```

Here the left side is a provisional name for a source-reviewed formal translation, not an API that
already exists.  Two honest closure routes are available:

1. accept the displayed richer-filter right side as the definition only after human/source review
   of its mesh, endpoint, and left-tag quantifiers; or
2. if an authoritative formal abstract Radon--Stieltjes predicate appears, prove the displayed
   equivalence to it.

The audit found no existing predicate capable of route 2.  Until route 1 is statement-checked or
route 2 is proved, Gate 1 remains open and Theorem 1.11.3 remains incomplete.

## J. External reuse and provenance

- Direct reuse: pinned Mathlib `Finset` order/union/sort APIs, `Set.Ici`,
  `map_val_Ici_atTop`, `atTop_Ici_eq`, `tendsto_comp_val_Ici_atTop`, and generic `Filter.Tendsto`
  composition.
- Adapted external code: none.
- PNT+ code copied: none.  If its `fromPoints` implementation is later closely ported, its
  Apache-2.0 and Aristotle/Harmonic provenance requirements must be preserved.
- External dependencies or Mathlib updates: none.

## K. CFC compatibility

Mathlib CFC remains the sole continuous functional calculus.  The new scratch work defines only
finite sums and filter implications.  It neither constructs a positive part by a second calculus
nor introduces a Borel functional calculus.  The eventual canonical comparison still targets the
existing `spectralProjectionIio`/CFC positive-part support theorem.

## L. Future PVM compatibility

The combinatorial candidate knows nothing about CFC, projections, or measures.  The abstract
bridge accepts any lower family `e`.  A future PVM can instantiate

```text
e(t) = E(Iio t),
e(t) - e(q) = E(Ico q t),
```

and use its simple-integral theory to provide `hmoment`.  The strict-lower endpoint and `[q,t)`
band convention are already the conventions verified by the scalar-atom and support tests.  No
future PVM should require rewriting the cofinal transport or fixed-projection proof.

## M. Public API decision

No new declaration should become public in this transaction.

- The bare `Ici` cofinality theorem already exists in pinned Mathlib.
- The `orderedCut` adapter has only one current consumer and should remain local until a second
  consumer establishes a stable abstraction boundary.
- The moment definitions and abstract bridge remain scratch-only because naming them
  “Radon--Stieltjes” publicly would imply a source semantics that has not been fixed.
- No PVM, resolution, spectral integral, or general integration object should be introduced.

## N. Sakai coverage

No additional source theorem is complete.  The transaction does, however, close three genuine
infrastructure questions:

1. prescribed finite cuts are handled by existing Mathlib `Ici` cofinality;
2. finite cut sets have a checked canonical ordered adapter with asymptotic extrema; and
3. arbitrary cofinal moment and endpoint limits imply exactly the translated and residual nets
   consumed by the support proof.

The next natural Sakai target remains Theorem 1.11.3 itself.  Work should not advance to Section
1.12 until the richer filter/source-equivalence gate is resolved or consciously deferred by human
review.

## O. Acceptance gates and assessment

| Gate | Status | Evidence or blocker |
|---|---|---|
| 0 — external audit | **PASS** | PNT+, teorth/analysis, pinned/current Mathlib, ICERM upstream, and original LeanOA audited exactly |
| 1 — source fidelity | **OPEN / RED** | Sakai does not define a refinement net; bare `Finset atTop` lacks shrinking mesh; richer filter/equivalence statement missing |
| 2 — directed refinement | **PASS FOR CANDIDATE** | `Finset` inclusion and union; full source index awaits Gate 1 |
| 3 — prescribed-cut insertion | **PASS** | insertion by finite union, including empty/singleton/duplicate/two-cut stress tests |
| 4 — cofinality | **PASS** | Mathlib `map_val_Ici_atTop`, `atTop_Ici_eq`, and scratch richer-filter eventual equality |
| 5 — limit preservation | **PASS ABSTRACTLY** | generic target-filter restriction and `hrefine : Tendsto refine lJ lD`; concrete source instantiation awaits Gate 1 |
| 6 — endpoint fidelity | **PASS ABSTRACTLY** | extrema escape for bare candidate; generic bridge retains endpoint residuals and assumes only asymptotic family limits |
| 7 — scratch-to-production support bridge | **OPEN** | exact analytic inputs are derivable conditionally; source filter and small positional assembly remain |
| 8 — uniqueness | **NOT CLOSED** | must not run ahead of Gates 1 and 7 |
| 9 — architecture | **PASS** | no duplicate CFC, PVM, resolution, or general integral; no production API added |
| 10 — validation | **PARTIAL** | focused scratch/build checks pass; full integrated Lean/lint/Verso/blueprint validation still required by lead |

Transaction assessment:

```text
IMPROVED
```

The result materially reduces uncertainty and removes cofinal transport, endpoint composition, and
translated-moment algebra as blockers.  It also prevents a false completion by isolating the mesh
/ source-equivalence gap.

Classification:

```text
COMBINATION:
  REUSABLE INFRASTRUCTURE
  EXTERNAL REUSE
  ARCHITECTURAL DECISION
  SOURCE HYPOTHESIS CLARIFICATION
  NEW BLOCKER
```

It is not a `SOURCE THEOREM` result.

## P. Version control and validation

Focused validation reported by the worker streams:

```text
lake env lean Scratch/DivisionRefinementCofinality.lean     PASS
lake env lean Scratch/FiniteCutEnumeration.lean             PASS
lake build LeanOA.Ultraweak.ProjectionDecomposition         PASS (3,047 jobs in bridge worktree)
lake env lean Scratch/SakaiRadonStieltjesBridge.lean         PASS, warning-free
git diff --check                                             PASS in each worker
placeholder/axiom scans of the three scratch files           PASS
```

The external-audit and this integration lane modify reports only.  The worker branches/worktrees
were:

```text
agent/rs-external-audit  /private/tmp/sakai-rs-external-1cd3a65
agent/rs-refinement      /private/tmp/sakai-rs-refinement-1cd3a65
agent/rs-bridge          /private/tmp/sakai-rs-bridge-1cd3a65
```

No worker pushed.  No dependency, production Lean module, umbrella import, Verso source, blueprint,
or shared coordination file was changed by this report.  Because Gate 1 remains open and no
production theorem was added, the report does not mark a Verso node complete.  A lead integration
run must still perform the full repository build, lint, Verso build/check, blueprint validation,
placeholder scan, and final clean-tree/commit audit.
