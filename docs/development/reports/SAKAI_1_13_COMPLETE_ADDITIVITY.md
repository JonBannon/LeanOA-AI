# Sakai 1.13 complete additivity

## Production decision

The complete-additivity characterization is implemented in:

```text
LeanOA.Ultraweak.CompleteAdditivity
```

The accepted API follows Outcome E: there is no public complete-additivity predicate, structure,
family wrapper, operator-sum notation, or second normality notion.  The source mathematics is
exposed by four theorems over the existing projection subtype, `HasSum`, projection `iSup`, and
`PositiveLinearMap.IsNormalOnProjections`.

## Source statement and quantifiers

Source: Sakai, *$C^*$-Algebras and $W^*$-Algebras*, Definition 1.13.4, printed p. 30
(local PDF p. 42).

Sakai begins with an arbitrary index set `I` and, in his words, a family
“of mutually orthogonal projections in M.”  For every finite subset `J ⊆ I`, he puts

```text
P_J = ∑_{α ∈ J} e_α.
```

The finite subsets are ordered by inclusion.  Their partial sums form a uniformly bounded,
increasing directed set.  Sakai defines the operator sum by

```text
∑_{α ∈ I} e_α = lub_J P_J.
```

He then writes: “From the proof of 1.13.2, we can easily see that normality is equivalent to
complete additivity.”  The parenthetical explanation quantifies over **arbitrary** mutually
orthogonal projection families and asserts

```text
φ (∑_{α ∈ I} e_α) = ∑_{α ∈ I} φ(e_α).
```

There is no countability, separability, enumeration, or sequence hypothesis.  The operator sum is
the least upper bound of the net of finite partial sums.  The scalar sum has the corresponding
unconditional finite-subsum semantics.

The source does not print a separate proof of the converse.  Its reference to the proof of 1.13.2
is terse but mathematically consequential: the formal proof reconstructs the chain/Zorn boundary
actually used by Sakai's cutoff and projection-selection argument.  It is not presented as a
verbatim proof omitted from the page.

Complete additivity here concerns positive linear functionals.  Definition 1.13.5 separately calls
an arbitrary ultraweakly continuous linear functional normal; no complete-additivity theorem for
arbitrary complex linear functionals is asserted in this module.

## Scalar summation semantics

For `f : ι → ℂ`, Mathlib's `HasSum f a` means convergence to `a` of the net of all finite subsums,
indexed by `Finset ι` and ordered by inclusion.  It supports an arbitrary index type and does not
impose countability.  It is preferable here to a bare `tsum` equality because `HasSum` records both
summability and the value rather than using a default value in the nonsummable case.

The module proves:

```lean
Complex.hasSum_iff_isLUB_finsetSum_of_nonneg
    {ι : Type u} {f : ι → ℂ} (hf : ∀ i, 0 ≤ f i) {a : ℂ} :
    HasSum f a ↔
      IsLUB (Set.range (fun s : Finset ι ↦ ∑ i ∈ s, f i)) a
```

Mathlib's `isLUB_hasSum` gives the forward implication.  The reverse implication uses
`Finset.sum_mono_set_of_nonneg`, `tendsto_atTop_isLUB`, and Sak-AI's
`Complex.instSupConvergenceClass`.  Mathlib's generic `hasSum_of_isLUB_of_nonneg` requires a
linear order, so it does not subsume this result for Sak-AI's partial order on `ℂ`.

Thus `HasSum` and the scalar finite-subsum LUB formulation are exactly equivalent in the positive
functional application.

## Public theorem API

The module introduces exactly these four declarations.

### Scalar bridge

```text
Complex.hasSum_iff_isLUB_finsetSum_of_nonneg
```

Its exact signature is displayed above.

### Normality implies complete additivity

```lean
PositiveLinearMap.IsNormalOnProjections.hasSum_orthogonal
    {M : Type u}
    [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] [WStarAlgebra M]
    {φ : M →ₚ[ℂ] ℂ} (hφ : φ.IsNormalOnProjections)
    {ι : Type v} (e : ι → {p : M // IsStarProjection p})
    (horth : Pairwise fun i j ↦ (e i).1 * (e j).1 = 0) :
    HasSum (fun i ↦ φ (e i).1) (φ (⨆ i, e i).1)
```

The index universe `v` is independent of the algebra universe `u`.

### Complete additivity implies normality

```lean
PositiveLinearMap.isNormalOnProjections_of_hasSum_orthogonal
    {M : Type u}
    [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] [WStarAlgebra M]
    (φ : M →ₚ[ℂ] ℂ)
    (hadd : ∀ {ι : Type u} (e : ι → {p : M // IsStarProjection p}),
      (Pairwise fun i j ↦ (e i).1 * (e j).1 = 0) →
      HasSum (fun i ↦ φ (e i).1) (φ (⨆ i, e i).1)) :
    φ.IsNormalOnProjections
```

### Characterization

```lean
PositiveLinearMap.isNormalOnProjections_iff_hasSum_orthogonal
    {M : Type u}
    [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] [WStarAlgebra M]
    (φ : M →ₚ[ℂ] ℂ) :
    φ.IsNormalOnProjections ↔
      ∀ {ι : Type u} (e : ι → {p : M // IsStarProjection p}),
        (Pairwise fun i j ↦ (e i).1 * (e j).1 = 0) →
        HasSum (fun i ↦ φ (e i).1) (φ (⨆ i, e i).1)
```

No proposition-valued abbreviation is hidden behind these statements.  The right-hand side is
written out deliberately.

## Normality implies complete additivity

Given an arbitrary orthogonal family `e`, the proof reuses:

```text
IsStarProjection.orthogonalFinsetSum
IsStarProjection.orthogonalFinsetSum_mono
IsStarProjection.isLUB_range_orthogonalFinsetSum
```

The canonical normality predicate sends the projection LUB of the finite partial sums to the
scalar LUB of their images under `φ`.  Linearity identifies

```text
φ (∑_{i ∈ J} e_i) = ∑_{i ∈ J} φ(e_i),
```

and `Complex.hasSum_iff_isLUB_finsetSum_of_nonneg` converts that scalar LUB to `HasSum`.

This direction uses no chosen predual, spectral projection, spectral approximation, spectral
integral, PVM, or polar decomposition.

## Complete additivity implies normality

The converse first targets the existing chain-restricted Scott-continuity interface rather than
attempting to reprove full normality directly.  For a nonempty projection chain `c` with LUB `q`,
it applies:

```text
IsChain.exists_orthogonal_projection_family
```

This supplies a set `s` of projections, its subtype-indexed orthogonal family, and:

1. every finite orthogonal partial sum is dominated by some member of `c`;
2. the supremum of the orthogonal family is `q`.

Complete additivity gives `HasSum (fun p : s ↦ φ p) (φ q)`.  The scalar bridge makes `φ q` the LUB
of the finite scalar subsums.  Finite domination shows that every such subsum is below some value
`φ r` with `r ∈ c`; conversely, monotonicity of `φ` bounds every `φ r` by `φ q`.  Therefore

```text
IsLUB (φ '' c) (φ q).
```

This is precisely the right-hand side of:

```text
PositiveLinearMap.isNormalOnProjections_iff_scottContinuousOn_chains
```

so the proof returns the canonical `IsNormalOnProjections` predicate.

The decomposition theorem encapsulates the maximal pairwise-orthogonal-family construction,
finite domination by a chain member, commutation at the orthogonal supremum, and the nonzero defect
projection which contradicts maximality unless the orthogonal supremum is `q`.  The chain-normality
bridge reuses the existing cutoff, projection-selection, corner real-rank-zero approximation,
strong-continuity, and continuous-dual characterization stack.  These are the formal counterparts
of the proof architecture referenced by Sakai.

The converse does not depend on the unresolved Section 1.11 spectral-integral/PVM boundary or on
the Section 1.12 element polar decomposition.

## Arbitrary cardinality and universes

The forward theorem has universes `u` and `v` and accepts `e : ι → Projection M` for every
`ι : Type v`, independently of `M : Type u`.  This is the direct arbitrary-cardinality source
statement.

The converse and iff quantify over `ι : Type u`.  This is sufficient rather than a countability
restriction: `IsChain.exists_orthogonal_projection_family` naturally indexes its maximal family by
a subtype of `Set (Projection M)`, which lies in the algebra's universe.  Complete additivity for
that same-universe family recovers normality.  The forward theorem then yields complete additivity
for families in every index universe.

A permanent family predicate with an internally quantified `Type v` would itself carry a fixed
universe parameter.  A set-indexed predicate could avoid that parameter, but would require an
additional range/repeated-zero bridge for arbitrary indexed orthogonal families.  Neither
abstraction is needed by the present consumers, so the theorem-only API avoids an unnecessary
foundational choice.

## Relationship with canonical normality

`PositiveLinearMap.IsNormalOnProjections` remains the sole intrinsic normality predicate.  The new
characterization composes with the existing production equivalences:

```text
complete additivity on arbitrary orthogonal projection families
  ↔ IsNormalOnProjections
  ↔ ScottContinuousOn projection chains
  ↔ ScottContinuous on projections
  ↔ ScottContinuous on all existing directed suprema
  ↔ ScottContinuousOn nonnegative directed families
  ↔ ScottContinuousOn bounded nonnegative directed families
  ↔ membership in the specified ultraweak continuous dual.
```

The relevant declarations include:

```text
PositiveLinearMap.isNormalOnProjections_iff_scottContinuousOn_chains
PositiveLinearMap.isNormalOnProjections_iff_scottContinuous
PositiveLinearMap.isNormalOnProjections_iff_scottContinuousOn_nonneg
PositiveLinearMap.isNormalOnProjections_iff_scottContinuousOn_bounded_nonneg
PositiveLinearMap.scottContinuous_iff_mem_continuousDual
PositiveLinearMap.scottContinuousOn_bounded_nonneg_iff_mem_continuousDual
```

Consequently the new theorem is also a characterization of Sakai's bounded directed-positive
normality and, with a specified predual, ultraweak continuity.  It adds no chosen-predual field or
new topology to its own statements.

## Reuse and overlap audit

The implementation reuses current Sak-AI's:

- canonical projection normality and all its Scott/continuous-dual bridges;
- arbitrary orthogonal finite sums and their projection LUB;
- projection-chain orthogonal decomposition;
- positive-map monotonicity and linearity;
- `ComplexOrder` supremum convergence.

Pinned and audited current Mathlib supply `HasSum`, `isLUB_hasSum`, finite sums,
`Finset.sum_mono_set_of_nonneg`, `ScottContinuousOn`, `IsChain`, `IsLUB`, and Zorn infrastructure.
Neither revision supplies the $W^*$-algebra projection-sum theorem, the chain decomposition, or the
complete-additivity/normality characterization.  As noted above, Mathlib's available converse from
a finite-subsum LUB requires a linear order and therefore does not cover the complex partial order.

The read-only original LeanOA supplies earlier specified-predual and ultraweak foundations, but it
does not contain the later projection-lattice, orthogonal-sum, chain-decomposition, chain-normality,
or complete-additivity APIs.  No result from that repository was duplicated under a new name.

Before introducing any new foundational theorem or proof pattern, search Mathlib, search the original LeanOA repository, and search the current Sak-AI repository for an existing theorem, definition, abstraction, or argument that already supplies the needed mathematics; reuse it where mathematically faithful, preserve architectural continuity with the APIs already built, and generalize only when that genuinely improves portability or reuse rather than duplicating local infrastructure.

## Generality and API rationale

- The scalar theorem is specific to nonnegative complex values because its missing ingredient is
  Sak-AI's scoped partial order and supremum-convergence instance on `ℂ`; its forward half reuses
  Mathlib generically.
- The forward operator-algebra theorem is stated at ordinary abstract $W^*$-algebra generality and
  has a completely independent index universe.
- The converse uses exactly the $W^*$-specific completeness needed by the projection-chain
  decomposition and exposes no predual implementation parameter.
- The pairwise-orthogonality convention matches the existing
  `IsStarProjection.orthogonalFinsetSum` API; no competing projection family object is introduced.
- Proof-local scalar and chain assembly remains inside the theorem proofs rather than expanding the
  permanent API.

## Validation and logical integrity

Focused validation commands:

```sh
lake env lean LeanOA/Ultraweak/CompleteAdditivity.lean
lake build LeanOA.Ultraweak.CompleteAdditivity
```

Both succeed.  The focused Lake build completed all 3,090 required jobs.

`#print axioms` for each of the four public declarations reports exactly:

```text
[propext, Classical.choice, Quot.sound]
```

Integrity audit:

```text
CUSTOM AXIOMS ADDED: 0
SORRY/ADMIT ADDED: 0
OTHER MATHEMATICAL PLACEHOLDERS ADDED: 0
COUNTABILITY RESTRICTIONS ADDED: 0
```
