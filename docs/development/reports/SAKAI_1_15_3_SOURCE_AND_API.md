# Sakai Theorem 1.15.3 — source and API audit

## Status

**SOURCE AUDIT COMPLETE; THEOREM NOT SOURCE-FORMALIZED.**

This report fixes the exact source statement, its prerequisites, the existing
Sak-AI endpoint it must target, and the first representation-neutral
infrastructure seam. It does not introduce a trace-class carrier and does not
claim any part of Theorem 1.15.3 as proved.

The source inspected directly was Shoichiro Sakai, *C\*-Algebras and
W\*-Algebras* (1971), local scan
`/Users/jonbannon/Desktop/ClaudeMath/SakaiBook_1971.pdf`.

- The Hilbert--Schmidt and trace-class preparation occupies printed pages
  35--38, PDF pages 47--50.
- Theorem 1.15.3 is on printed page 39, PDF page 51.

## Exact source statement

Let `H` be a complex Hilbert space, let `B(H)` be its bounded operators, let
`T(H)` be the Banach space of trace-class operators with

```text
‖a‖₁ = Tr(|a|),
```

and let `B(H)_*` be Sakai's previously constructed norm closure of the finite
vector-functional space. Define

```text
φₐ(x) = Tr(xa).
```

Theorem 1.15.3 asserts both:

1. `a ↦ φₐ` is a linear isometric identification of `T(H)` with `B(H)_*`;
2. under this identification, positive trace-class operators correspond
   exactly to positive elements of `B(H)_*`.

“Identification” must therefore become a linear isometric equivalence, not
only an injection, dense-range map, or algebraic linear equivalence. The
positivity sentence is part of the theorem and must be proved in both
directions.

## Translation conventions

Sakai's scalar product is linear in its first argument. Mathlib's complex
inner product is conjugate-linear in its first argument. Thus

```text
(x ξ, η)_Sakai = ⟪η, x ξ⟫_ℂ
```

and the current Sak-AI vector functional has the correct orientation.

The source-facing pairing must retain the printed multiplication order

```text
Tr(x * a),
```

even though trace cyclicity later gives `Tr(a * x)`.

The theorem assumes an arbitrary complex Hilbert space. No separability,
nontriviality, finite-dimensionality, factor, or unital-subalgebra hypothesis
may be added. In a nonseparable Hilbert space, a trace-class operator still
has separable effective support; a formal construction must prove the needed
countability rather than assume it globally.

“Positive in `B(H)_*`” means that the represented norm-continuous functional
is positive on positive operators. Sak-AI's short concrete-predual carrier is
not presently equipped with an order instance. The eventual theorem should
first state positivity through the represented functional or an existing
`PositiveLinearMap`; it must not add an order instance merely to make the
source sentence look shorter.

## Source dependency chain

The four pages preceding the theorem establish the following mathematics.

1. For a complete orthonormal system `(ξᵢ)`, Sakai defines

   ```text
   ‖a‖₂² = ∑ i, ‖a ξᵢ‖²
   ```

   and proves basis independence.
2. The Hilbert--Schmidt class is a Hilbert space, is stable under adjoint and
   left/right multiplication by bounded operators, and consists of compact
   operators.
3. For a positive bounded operator `h`, Sakai defines

   ```text
   Tr(h) = ∑ i, (h ξᵢ, ξᵢ)
   ```

   and proves basis independence.
4. A bounded operator is trace class when `Tr(|a|) < ∞`; equivalently it is a
   product of two Hilbert--Schmidt operators.
5. The complex trace on trace class is linear, star compatible, and cyclic
   against bounded operators:

   ```text
   Tr(a * b) = Tr(b * a).
   ```

6. The functional `φₐ(x) = Tr(xa)` is bounded and satisfies the exact norm
   identity

   ```text
   ‖φₐ‖ = Tr(|a|) = ‖a‖₁.
   ```

7. `T(H)` is complete for the trace norm.
8. Compact spectral approximation of `|a|` gives trace-norm approximation of
   `a` by finite-rank operators.
9. Finite-rank trace functionals lie in the finite vector-functional space,
   while a rank-one calculation represents every vector functional by a
   trace-class operator.
10. Closedness and the two inclusions identify the image of trace class with
    the previously constructed `B(H)_*`.

The positivity correspondence is printed in Theorem 1.15.3 but is not
expanded into a separate proof in the inspected passage. It remains an
explicit formal proof obligation.

## Logical relation to Proposition 1.15.2

The source derivation of Theorem 1.15.3 does not use Proposition 1.15.2. The
relevant earlier dependency is the definition of `B(H)_*` as the norm closure
of finite WOT-continuous vector functionals. The preceding proposition is
complete for source order, but its bounded-topology homeomorphisms are not a
mathematical prerequisite for the trace-class representation theorem.

## Existing Sak-AI endpoint that must be reused

The predual side is already complete and must not be rebuilt. The eventual
isometry must target

```lean
ContinuousLinearMap.VectorFunctionalPredual ℂ H H
```

and reuse at least the following public API:

- `ContinuousLinearMap.vectorFunctionalPredualEquivClosure`;
- `ContinuousLinearMap.vectorFunctionalInPredual`;
- `ContinuousLinearMap.vectorFunctionalSpanToPredual` and
  `vectorFunctionalSpanToPredualₗᵢ`;
- `ContinuousLinearMap.denseRange_vectorFunctionalSpanToPredual` and
  `dense_vectorFunctionalPredualSpan`;
- `ContinuousLinearMap.vectorFunctionalPredualEquivDual`;
- `ContinuousLinearMap.vectorFunctionalPredual_predualEquivDual_apply_apply`;
- `ContinuousLinearMap.vectorFunctionalPredualEvaluation_vectorFunctionalInPredual`;
- `Predual.toDualₗᵢ`.

These declarations realize exactly Sakai's norm closure of finite vector
functionals. Introducing another `B(H)_*`, another predual class, or a
trace-class carrier defined to be this predual would be circular and would
not source-formalize the theorem.

The operator and functional layers already provide useful later ingredients:

- Mathlib `InnerProductSpace.rankOne`, `rankOne_apply`, `norm_rankOne`,
  `comp_rankOne`, `rankOne_comp_rankOne`, and `adjoint_rankOne`;
- Mathlib `ContinuousLinearMap.IsPositive` and the Loewner order on Hilbert-
  space endomorphisms;
- Mathlib `CFC.abs`, `CFC.abs_nonneg`, `CFC.abs_mul_abs`, and `CFC.norm_abs`;
- Sak-AI `WStarAlgebra.existsUnique_element_polar_decomposition`;
- Sak-AI's `PositiveLinearMap` normality APIs and
  `Ultraweak.functionalAbs`.

With Mathlib's convention, the finite-dimensional calculation has the exact
desired orientation:

```text
Tr(T ∘ rankOne ξ η) = ⟪η, T ξ⟫_ℂ.
```

The available `InnerProductSpace.trace_rankOne` proves only the finite-
dimensional version and is evidence for orientation, not the required
infinite-dimensional trace theorem.

## Pinned and current Mathlib audit

The pinned dependency is commit
`476ab284693e554a6b48c5f5210cb4fb5ae51252`. The available later local audit
snapshot is commit `be865aa50cc0364be66c3941a6dc0c845a2c2ceb` from 2026-08-31.
The official Mathlib `master` trace and singular-value sources were also
rechecked on 2026-09-02:

- [current `Trace.lean`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Analysis/InnerProductSpace/Trace.lean);
- [current `SingularValues.lean`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Analysis/InnerProductSpace/SingularValues.lean).

The conclusion is unchanged in all three snapshots.

### What is not available

No operator-theoretic declaration or module was found for:

- infinite-dimensional Hilbert--Schmidt operators;
- trace-class or Schatten-class operators;
- nuclear operators;
- a trace norm;
- a basis-independent positive trace on arbitrary Hilbert spaces.

Mathlib's general `LinearMap.trace` is not a substitute. Its definition uses
a finite basis when one exists and returns zero otherwise. Consequently its
cyclicity lemmas and `tracePositiveLinearMap` do not express the trace in
Sakai 1.15.3 outside finite dimension. Using them at the source boundary
would silently prove the wrong theorem.

`LinearMap.singularValues` is likewise finite-dimensional. The current file
explicitly lists infinite-dimensional approximation numbers as future work.

### Reusable Mathlib primitives

The audit did find the following genuine inputs:

- arbitrary-index Hilbert bases and Parseval expansions:
  `HilbertBasis.repr`, `HilbertBasis.hasSum_repr`,
  `HilbertBasis.hasSum_inner_mul_inner`,
  `HilbertBasis.summable_inner_mul_inner`,
  `HilbertBasis.tsum_inner_mul_inner`, `HilbertBasis.finite_spans_dense`, and
  `exists_hilbertBasis`;
- Bessel estimates:
  `Orthonormal.inner_products_summable` and
  `Orthonormal.tsum_inner_products_le`;
- adjoints, rank-one operators, infinite sums, `lp`, and ENNReal sums;
- compact operators through `IsCompactOperator` and `compactOperator`, with
  composition and norm-limit closure;
- the compact self-adjoint spectral facts
  `ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot` and
  `ContinuousLinearMap.finite_dimensional_eigenspace`.

The compact spectral API does not enumerate the nonzero eigenspaces or give
an operator-series expansion. No ready finite-rank-density theorem in trace
norm exists because the trace norm itself is absent.

Original LeanOA at commit `cb811c1006ae78a0ff1d175253200e1859843370`
contains none of the missing trace/Hilbert--Schmidt infrastructure.

## Formalization gap

An honest proof of Theorem 1.15.3 still requires:

1. a basis-independent extended positive trace;
2. Hilbert--Schmidt energy/norm, adjoint invariance, ideal estimates,
   completeness, and compactness;
3. a trace-class operator predicate/carrier equivalent to finiteness of
   `Tr(|a|)`;
4. the trace norm and its Banach-space structure;
5. the complex trace and cyclicity against bounded operators;
6. the bounded trace pairing `a ↦ (x ↦ Tr(xa))` and its exact norm;
7. finite-rank density in trace norm and the rank-one coefficient formula;
8. surjectivity onto the existing vector-functional predual;
9. positivity preservation and reflection.

This is a substantial new foundation, not a short wrapper around the current
predual theorem.

## Route comparison

### A. Sakai's Hilbert--Schmidt route

This has the highest source fidelity and produces the standard operator-side
objects needed later. It requires the longest initial prerequisite chain, but
none of that work is artificial: Hilbert--Schmidt and trace-class ideals are
independently important operator-algebra infrastructure.

### B. Nuclear/rank-one completion

A projective or nuclear completion of finite-rank operators aligns closely
with the already completed vector-functional predual and could shorten the
eventual isometry/density argument. Current Mathlib, however, has no completed
projective tensor product or nuclear-operator carrier with the needed
separation and universal properties. Defining the carrier as the existing
predual would be circular. An honest nuclear route is therefore another
major foundation, not a free shortcut.

A shorter source-faithful variant deserves a later scratch test.  One may
associate to the existing coefficient predual element `p` the unique bounded
operator `Aₚ` characterized by

```text
⟪η, Aₚ ξ⟫ = p(rankOne ξ η).
```

Finite-rank compression nets and the bounded topology agreement from
Proposition 1.15.2 should make this realization injective.  On positive
elements, arbitrary-basis diagonal sums and square-root vector-functional
series offer a route to proving finite positive trace.  The existing
functional and element polar decompositions could then extend the result to
general elements and identify the operator modulus.  Conversely, finite
positive trace should reconstruct a predual element from the same square-root
series.

This is not a license to define trace class as the predual.  It is an
operator-range proof strategy: the public trace-class predicate must still be
defined independently by `Tr(|a|) < ∞`, and the range equivalence must be
proved before the resulting carrier can be called trace class.  The route may
avoid assembling the full Hilbert--Schmidt Banach ideal before Theorem 1.15.3,
but it still depends on a genuine basis-independent positive trace and on the
operator-realization arguments just described.

### C. Compact-positive spectral sums

Compact positive spectral expansions are useful for finite-rank
approximation and for computing the trace, but current Mathlib stops before
an enumerated eigenbasis/operator-series theorem. This route also does not by
itself supply the Banach ideal and trace-norm triangle inequality. It should
support, rather than replace, either of the first two routes.

The permanent trace-class carrier remains a consequential architectural
choice between an honest Hilbert--Schmidt-first implementation and this
source-faithful predual-range hybrid. This audit does not make that choice.
No escalation is required yet because the next prerequisite is common,
reversible, and representation-neutral.

## Next bounded transaction

Scratch-test and then, if the API remains clean, prove the basis-independent
Hilbert--Schmidt energy identity for a continuous linear map between arbitrary
Hilbert spaces. For Hilbert bases `e` of `E` and `f` of `F`, the target is the
extended-nonnegative-real equality

```text
∑' i, ‖T (e i)‖ₑ² = ∑' j, ‖T† (f j)‖ₑ².
```

The proof should expand both sides into the same double sum of matrix-
coefficient norms and use arbitrary-index Tonelli/`tsum` interchange. It
must:

- work for arbitrary index types and hence not assume separability;
- be generalized to `RCLike` scalars and maps `E →L[𝕜] F` if the available
  adjoint/Parseval APIs permit;
- remain an equality in `ℝ≥0∞`, so no summability hypothesis is hidden;
- imply independence of the domain Hilbert basis and adjoint invariance;
- introduce no Hilbert--Schmidt or trace-class carrier during the scratch
  transaction.

This lemma is a direct prerequisite of Sakai's Hilbert--Schmidt definition
and remains useful under a later nuclear or spectral implementation. Only
after it is kernel-checked should the project decide whether the production
semantic core begins with Hilbert--Schmidt energy or with a separately
justified nuclear completion.

## Source status

```text
Sakai Theorem 1.15.3 statement: SOURCE-CHECKED
Sakai Theorem 1.15.3 prerequisites: SOURCE-MAPPED
Sakai Theorem 1.15.3: NOT SOURCE-FORMALIZED
```
