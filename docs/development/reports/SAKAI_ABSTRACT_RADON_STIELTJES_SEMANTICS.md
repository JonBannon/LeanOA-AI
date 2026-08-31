# Sakai's abstract Radon--Stieltjes integral: source-semantics audit

Status: **LEVEL C — GENUINE AMBIGUITY; Sakai 1.11.3 is NOT SOURCE-FORMALIZED**

Audit date: 2026-08-30

This report distinguishes what the source fixes from a useful modern Lean model. The current
Sak-AI candidate is

```text
stieltjesFilter =
  (atTop : Filter (Finset ℝ)) ⊓ comap divisionMesh (nhds 0)
```

with left-endpoint identity moments, asymptotic endpoint limits, and prescribed-cut cofinality.
Its downstream support and uniqueness consequences are kernel-checked. That success does not by
itself identify the candidate with Sakai's undefined terminology.

## A. Sakai internal evidence

### A.1 The topology is explicitly strong

The decisive source correction is typographical but not ambiguous after comparison with Sakai's
own definitions:

- printed p. 2 / PDF p. 14 defines Greek `σ(M,M_*)` as the weak-star, weak, or `σ` topology;
- printed p. 20 / PDF p. 32, Definition 1.8.6, defines Latin `s(M,M_*)` from the seminorms
  `x ↦ φ(x* x)^(1/2)` and calls it the strong or `s` topology;
- Theorem 1.8.9 on that page orders
  `σ(M,M_*) ≤ s(M,M_*) ≤ s*(M,M_*) ≤ τ(M,M_*)`, with the topology on the right stronger;
- printed p. 35 / PDF p. 47 identifies `s(M,M_*)` on bounded spheres with the strong operator
  topology in a concrete von Neumann algebra;
- the subject index, printed p. 253 / PDF p. 265, lists `s`/strong and `σ`/weak separately.

Direct high-resolution inspection of printed p. 26 / PDF p. 38 shows Latin `s(M,M_*)` in Lemma
1.11.1, clause 2 of Theorem 1.11.3, and the sentence defining the topology of the abstract
Radon--Stieltjes integral. Earlier Sak-AI reports which read this glyph as `σ` were wrong.

### A.2 What Section 1.11 supplies

Section 1.11 occupies printed pp. 26--27 / PDF pp. 38--39. For a self-adjoint `x`, it constructs

```text
e(λ) = support ((λ 1 - x)⁺).
```

Theorem 1.11.3's existence proof chooses a finite strictly increasing division of
`[-‖x‖-δ, ‖x‖+δ]` with adjacent gaps below `ε`, forms the lower- and upper-endpoint sums

```text
m(Δ) = Σ λᵢ₋₁ (e(λᵢ) - e(λᵢ₋₁)),
M(Δ) = Σ λᵢ   (e(λᵢ) - e(λᵢ₋₁)),
```

and proves `m(Δ) ≤ x ≤ M(Δ)` and `M(Δ)-m(Δ) ≤ ε 1` before letting `ε → 0`.
The only earlier division convention located in the book, printed p. 6 / PDF p. 18, likewise gives
ordered endpoints and an adjacent-gap bound, not a refinement order.

The uniqueness paragraph splits the abstract integral at an arbitrary `λ₀`. This requires interval
additivity or an equivalent prescribed-cut property. It is good evidence that a faithful semantics
must support that split, but it does not say whether the mechanism is refinement-directed
partitions, insertion into mesh-fine partitions, an established additivity theorem, or a
measure-theoretic integral.

The source supports the strict lower-family convention `e(r)=E(Iio r)` and bands `[q,r)`: the
uniqueness proof uses `e(r-0)=e(r)`. It gives asymptotic endpoints. It does not specify whether the
whole-line integral is a joint endpoint-and-mesh limit, an iterated compact truncation, or a net of
all bounded divisions.

### A.3 Exhaustive negative evidence

All 270 PDF pages were OCR-searched and relevant pages visually checked. The mathematical word
“Stieltjes” occurs only once, in Theorem 1.11.3. There is no local definition, footnote, exercise,
remark, concluding attribution, or citation. The index contains `Spectral resolution 26` but no
entry for Radon--Stieltjes, Riemann--Stieltjes, abstract integral, resolution of identity, or
operator-valued integration.

Sakai's bibliography includes Hille--Phillips [75], Bourbaki [18], Segal [184], and Dixmier, but
none is cited in Section 1.11. Uses elsewhere in the book do not license treating any one of them
as the definition governing this theorem.

Thus Sakai explicitly fixes:

- the target topology `s(M,M_*)`;
- finite ordered cuts and shrinking adjacent gaps in the existence proof;
- lower- and upper-endpoint sums;
- the strict `Iio`/`Ico` atom convention;
- asymptotic endpoint behavior;
- enough integral additivity to split at an arbitrary cut.

He does not explicitly fix:

- a directed index or filter;
- a refinement order;
- arbitrary versus endpoint tags;
- prescribed-cut cofinality as an indexing theorem;
- a joint versus iterated improper-endpoint limit.

## B. Historical-source evidence

No item in this table is an explicit citation governing Section 1.11.

| Source | Definition/pages | Topology | Partitions, refinement, tags, endpoints | Integrator / integrand | Evidential conclusion |
| --- | --- | --- | --- | --- | --- |
| E. Hille and R. Phillips, *Functional Analysis and Semi-Groups*, revised ed. (1957) | §3.3, pp. 62--63; related discussion through p. 66 ([Google Books](https://books.google.com/books?id=fs0-AAAAIAAJ&pg=PA62)) | Limit “in a given topology”; the integral is relative to that topology | Fixed compact `[a,b]`; finite subdivisions; arbitrary in-band tags; maximum mesh tends to zero; no refinement order or improper endpoint convention in this definition | Vector integrand with scalar BV integrator, or scalar integrand with vector integrator | Closest contextual match, including Sakai's phrase “with respect to” a topology. Sakai lists the book but does not cite it here; it says *Riemann--Stieltjes*, not *Radon--Stieltjes*. |
| Hille--Phillips (1957) | pp. 76--77 | A given topology | Measurable subdivisions directed by further refinement; tags in measurable pieces | Vector-valued Lebesgue-type integration against a measure | Shows that refinement-directed semantics also existed in the same book, but as a different measurable-space integral, not the interval Riemann--Stieltjes definition. |
| M. Gowurin, “Über die Stieltjessche Integration abstrakter Funktionen,” *Fund. Math.* 27 (1936), 254--265 | §3, pp. 258--259; separate Radon construction in §6, pp. 264--265 ([EuDML](https://eudml.org/doc/212873)) | Norm convergence in a complete normed target | Fixed compact interval; arbitrary tags; mesh tends to zero; no refinement net | Abstract/vector-valued integrand and integrator combined by a continuous bilinear product | Defines abstract Stieltjes and Radon integrals separately, evidence against a uniform compound-term convention. |
| S. Izumi and G. Sunouchi, “Notes on Banach Space (VI),” *Proc. Imperial Academy* 19 (1943), 169--173 | pp. 170--171 ([J-STAGE PDF](https://www.jstage.jst.go.jp/article/pjab1912/19/4/19_4_169/_pdf/-char/ja)) | Scalar testing relative to a chosen family of linear functionals | Inherits either scalar Lebesgue--Stieltjes or Riemann--Stieltjes semantics; no universal endpoint convention | Scalar function against an abstract/vector integrator | Explicitly treats abstract Riemann--Stieltjes and abstract Radon integration as separate notions. |
| P. J. Daniell, “A General Form of Integral,” *Ann. Math.* 19 (1918), 279--294 | pp. 279--281 ([primary PDF](https://www.tu-chemnitz.de/mathematik/analysis/pictures/Daniell-18.pdf)) | Scalar functional integration | Monotone/Daniell extension, not tagged partitions; infinite bounds are allowed | Scalar integrands; integrator encoded by a functional/measure | Uses “Radon or Young--Stieltjes” for a measure/Daniell extension, a materially different construction. |
| M. M. Rao, “Linear Functionals on Orlicz Spaces,” *Pacific J. Math.* 25 (1968), 553--589 | p. 571 ([primary PDF](https://msp.org/pjm/1968/25-3/pjm-v25-n3-p13-p.pdf)) | Scalar convergence | Finite measurable partitions ordered by refinement; no tags or real endpoints | Bounded finitely additive set function and lattice/Orlicz integrand | Uses the near-exact phrase “abstract Radon-Stieltjes type” for measurable-set refinement semantics unrelated to interval mesh sums. |

The period evidence is therefore not uniform enough for LEVEL B certification.

## C. Candidate interpretations

Four interpretations remain genuinely plausible at different levels:

1. A Hille--Phillips-style, topology-parametric Riemann--Stieltjes limit on every compact
   truncation, specialized to `s(M,M_*)`, followed by an unspecified improper endpoint limit.
2. A Daniell/Radon/Lebesgue--Stieltjes construction obtained after scalarization or construction of
   a projection-valued measure.
3. A scalar-testing definition against a class of functionals, with a later reconstruction theorem.
4. The current Sak-AI joint refinement-plus-mesh whole-line filter with left-endpoint tags and
   asymptotic extrema.

Sakai's existence calculation resembles (1); his uniqueness split is natural under (1), (2), or a
coherent version of (4). The compound terminology and absent citation do not distinguish them.

## D. Comparison to Sak-AI

| Interpretation / coordinate | Relation to the checked candidate | Status |
| --- | --- | --- |
| Sakai's target topology | Strong convergence of the *same net* implies the candidate's ultraweak convergence | **PROVED** in `Scratch.SakaiStrongRadonStieltjesBridge.tendsto_toUltraweak_of_tendsto_toStrong` |
| Full strong version of the current finite-cut candidate | Implies the checked pointwise uniqueness theorem after topology forgetting | **PROVED** in `competing_eq_spectralProjectionIio_of_strong_finset_candidate` |
| Candidate ultraweak topology versus source strong topology | Candidate is weaker on this coordinate; no converse is claimed | **SOURCE ⇒ CANDIDATE only for the same net** |
| Sakai's finite cuts/gap control | Compatible with `orderedCut` and `divisionMesh` | **COMPATIBLE**, not a definition equivalence |
| Sakai's lower sums | Compatible with current left-endpoint identity moments | **COMPATIBLE**, not evidence that arbitrary tags are excluded |
| Prescribed-cut split | Current filter proves eventual insertion; Sakai's proof needs a split but does not specify its indexing mechanism | **UNCLEAR** |
| Hille--Phillips compact tagged mesh limit | Likely implies a restricted left-tag subsystem on a fixed compact interval, but tag independence, truncation, endpoints, and strong-to-ultraweak bridges are all needed | **UNCLEAR; not definitionally the same** |
| Gowurin norm Riemann--Stieltjes | Norm is stronger on the topology coordinate, but the fixed-compact arbitrary-tag and endpoint models differ | **UNCLEAR overall; stronger only topologically** |
| Scalar-testing / Daniell / measurable-refinement readings | Require construction and comparison of a measure or scalar reconstruction before they can be related | **UNCLEAR / no equivalence proved** |

The overall relation between Sakai's phrase and the current candidate is therefore:

```text
UNCLEAR
```

It is not definitionally the same, not proved equivalent, and not globally classified as stronger
or weaker because the topological coordinate and the indexing/endpoint coordinates differ.

## E. Certification level

```text
LEVEL C — GENUINE AMBIGUITY
```

There is LEVEL A evidence for the printed topology, finite ordered cuts, endpoint sums, gap control,
and strict half-open convention. There is no LEVEL A evidence for the actual integral net/filter,
tag quantification, refinement order, or improper-limit convention. The historical literature is
too nonuniform and too weakly tied to Section 1.11 to reach LEVEL B.

## F. Formalization consequence

```text
Sakai Theorem 1.11.3: NOT SOURCE-FORMALIZED
```

No `HasRadonStieltjesRepresentation`, arbitrary lower-resolution structure, operator-valued
integral, or PVM predicate earns production status from this audit. No semantic equivalence is
postulated.

The refinement-plus-mesh theorem remains a fully kernel-checked clarified formal analogue under an
explicit hypothesis. The new strong-to-ultraweak scratch bridge proves exactly the safe implication
which is independent of the unresolved historical index semantics. Nothing downstream is
re-proved.

The ambiguity need not freeze the book. Development may proceed to Section 1.12 wherever it uses
the canonical lower spectral family and its proved conclusions rather than a source-level abstract
integral predicate. A natural preceding bounded task is to promote the canonical strong-topology
continuity statement corresponding exactly to Sakai 1.11.1.
