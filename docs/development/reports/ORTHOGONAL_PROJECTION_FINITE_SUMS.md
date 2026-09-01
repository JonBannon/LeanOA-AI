# Orthogonal projection finite partial sums

## Scope and source

This is Workstream 1.13-B. The source is Sakai, *$C^*$-Algebras and $W^*$-Algebras*,
Definition 1.13.4, printed p. 30 (local scan p. 42), inspected directly at
`/Users/jonbannon/Desktop/ClaudeMath/SakaiBook_1971.pdf`.

Sakai starts with an arbitrary family `(eα)_{α∈I}` of mutually orthogonal projections. For
each finite subset `J ⊆ I`, he sets

```text
P_J = Σ_{α∈J} eα.
```

Ordered by inclusion of finite subsets, `(P_J)` is an increasing, uniformly bounded directed net.
Sakai first states ultraweak convergence to its least upper bound and then proves convergence in
`s(M,M_*)`; the limit is a projection. He defines the sum of the arbitrary family to be this least
upper bound. The last sentence of 1.13.4 relates normality to complete additivity; that separate
functional statement is not part of this workstream.

## Existing infrastructure reused

The implementation reuses, rather than replaces:

- Mathlib finite-sum distribution, `isSelfAdjoint_sum`, and star-projection order lemmas;
- Sak-AI's complete lattice on `{p : M // IsStarProjection p}`;
- `IsStarProjection.isLUB_coe_of_isLUB` for passage to the ambient $C^*$-algebra order;
- `IsStarProjection.tendsto_toUltraweak_of_isLUB`;
- `Ultraweak.Strong.tendsto_toStrong_of_isLUB`.

Pinned Mathlib at `476ab284693e554a6b48c5f5210cb4fb5ae51252` and the audited current Mathlib
checkout at `be865aa50cc0364be66c3941a6dc0c845a2c2ceb` contain the algebraic ingredients but
no arbitrary orthogonal-projection finite-subset LUB or convergence theorem. The read-only
original LeanOA at `cb811c1006ae78a0ff1d175253200e1859843370` does not contain the later
projection-lattice or intrinsic-strong convergence layer.

## Lean formulation

The production module is:

```text
LeanOA.Ultraweak.OrthogonalProjectionSum
```

The family is represented without a new structure:

```lean
p : I → {q : M // IsStarProjection q}
horth : Pairwise fun i j ↦ (p i).1 * (p j).1 = 0
```

Its finite partial sum is the projection-valued function

```lean
IsStarProjection.orthogonalFinsetSum p horth : Finset I → {q : M // IsStarProjection q}
```

No infinite-sum notation or repository-specific projection-family structure is introduced. The
sum of the full family is represented by the existing projection supremum `⨆ i, p i`.

## Public declarations

### Algebraic layer

```text
IsStarProjection.finset_sum
IsStarProjection.orthogonalFinsetSum
IsStarProjection.coe_orthogonalFinsetSum
IsStarProjection.orthogonalFinsetSum_mul_eq_zero_of_disjoint
IsStarProjection.coe_orthogonalFinsetSum_union_of_disjoint
```

`finset_sum` is stated at `NonUnitalNonAssocSemiring` plus `StarAddMonoid` generality, and the
bundled finite-sum construction is computable. Mathlib's `OrthogonalIdempotents` theorem currently
requires a unital `Semiring`; the short direct finite-sum proof avoids imposing that irrelevant
unit and associativity. This is a plausible small Mathlib generalization, but remains in the new
theorem module for now because moving it into the mirrored projection junction is unnecessary for
the present consumer.

The two disjoint-set lemmas give the smallest finite decomposition interface needed by later
complete-additivity arguments. General common refinement needs no further declaration: union is a
common upper bound, and monotonicity applies to the two subset inclusions.

### Ordered nonunital $C^*$-algebra layer

```text
IsStarProjection.orthogonalFinsetSum_mono
IsStarProjection.le_orthogonalFinsetSum_of_mem
```

These require no unit, $W^*$-algebra, or topology. Monotonicity states exactly that finite-subset
inclusion makes the partial sums an increasing net.

### $W^*$-algebra lattice and topology layer

```text
IsStarProjection.orthogonalFinsetSum_le_iSup
IsStarProjection.isLUB_range_orthogonalFinsetSum
IsStarProjection.isLUB_range_coe_orthogonalFinsetSum
IsStarProjection.tendsto_toUltraweak_orthogonalFinsetSum
IsStarProjection.tendsto_toStrong_orthogonalFinsetSum
```

The first LUB theorem is internal to the canonical projection lattice. The second records the same
least-upper-bound statement in the ambient $C^*$-algebra order, matching Sakai's source-facing
formulation. The convergence proofs do not reconstruct compactness or seminorm estimates: they
apply the existing projection-LUB theorems and precompose with the cofinal map from `Finset I` to
the range of the partial-sum net.

The topological statements expose a specified predual `P` only because their codomains are the
existing types `σ(M,P)` and `Ultraweak.Strong M P`. The algebraic and lattice statements expose no
chosen predual.

## Cardinality and boundedness

`I` is an arbitrary type. There is no `Countable I`, `Fintype I`, enumeration, sequence, `tsum`, or
`Summable` hypothesis. The Moore--Smith index is `Finset I` with its inclusion order and `atTop`.

Every partial sum is a projection, so Mathlib's `IsStarProjection.norm_le` gives the uniform norm
bound by one. More intrinsically, `orthogonalFinsetSum_le_iSup` bounds every partial sum by the
limiting projection itself.

## Source coverage and next use

This module formalizes the geometric and convergence content used to define Sakai's arbitrary
orthogonal projection sum in 1.13.4. It does not yet formalize the final normality/completely-
additive equivalence in that definition, so Definition 1.13.4 should not yet be marked wholly
source-formalized.

The immediate downstream use is the forward implication

```text
normal positive functional
  ⇒ preservation of the LUB of the finite partial sums
  ⇒ complete additivity on arbitrary orthogonal projection families.
```

That result should use the LUB theorem here and the source-normality bridge. It should continue to
formulate arbitrary scalar sums through finite partial sums rather than ordinary `tsum`.

## Validation and logical integrity

The module passes direct Lean elaboration and its focused Lake build. Principal declarations have
only the standard foundational dependencies:

```text
[propext, Classical.choice, Quot.sound]
```

No custom axiom, `sorry`, `admit`, opaque assumption, or mathematical placeholder is present.
