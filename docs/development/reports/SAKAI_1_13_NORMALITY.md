# Sakai 1.13 normality bridge

## Source

The source was inspected directly in Sakai, *$C^*$-Algebras and $W^*$-Algebras*, printed
pp. 28--30 (local PDF pp. 40--42).

Definition 1.13.1 says that a **positive linear functional** `φ` on a $W^*$-algebra `M` is
normal when

```text
φ (l.u.b._α x_α) = l.u.b._α φ(x_α)
```

for every uniformly bounded increasing directed set `{x_α}` of positive elements of `M`.
The quantifier is over arbitrary directed sets, not sequences. “Uniformly bounded” is norm
boundedness. The definition is order-theoretic: it asserts equality of an operator least upper
bound and a scalar least upper bound, not convergence in a topology.

Theorem 1.13.2 assumes `φ` positive and states that this normality condition is equivalent to
continuity for `σ(M,M_*)`. The source proves ultraweak continuity implies normality by citing
1.7.4. For the converse it uses the maximal cutoff-projection, projection-selection, corner
approximation, and strong-to-ultraweak arguments already formalized in Sak-AI's normality stack.

The remainder of the section contains unique predual Corollary 1.13.3, arbitrary orthogonal
projection sums and complete additivity in Definition 1.13.4, and the terminology “normal linear
functional” for an ultraweakly continuous linear functional in Definition 1.13.5. Those items are
not redefined in this module.

## Lean formulation

The canonical permanent predicate remains

```lean
PositiveLinearMap.IsNormalOnProjections
```

No new normal-functional predicate or structure was introduced. Sakai's literal family condition
is represented by Mathlib's existing restricted Scott continuity:

```lean
ScottContinuousOn
  {s : Set M | Bornology.IsBounded s ∧ ∀ x ∈ s, 0 ≤ x} φ
```

`ScottContinuousOn` supplies exactly the remaining source quantifiers: the set is nonempty and
directed, an element `a` is supplied with `IsLUB s a`, and the conclusion is
`IsLUB (φ '' s) (φ a)`. This avoids choosing a supremum operation or imposing a sequential
interpretation.

The explicit boundedness clause is redundant inside this formulation. If a nonnegative set `s`
has least upper bound `a`, then `0` is a lower bound and `a` is an upper bound, hence
`isBounded_of_bddAbove_of_bddBelow` makes `s` norm bounded. The general theorem

```lean
ScottContinuousOn.bounded_nonneg_iff_nonneg
```

records this fact at nonunital $C^*$-algebra generality for an arbitrary map into a preorder.

## Public declarations

The new production module is `LeanOA.Ultraweak.NormalOrder`. Its public surface is:

```text
ScottContinuousOn.bounded_nonneg_iff_nonneg
PositiveLinearMap.isNormalOnProjections_iff_scottContinuous
PositiveLinearMap.isNormalOnProjections_iff_scottContinuousOn_nonneg
PositiveLinearMap.isNormalOnProjections_iff_scottContinuousOn_bounded_nonneg
PositiveLinearMap.scottContinuous_iff_mem_continuousDual
PositiveLinearMap.scottContinuousOn_bounded_nonneg_iff_mem_continuousDual
```

The first three intrinsic normality comparisons use the ordinary Mathlib
`[WStarAlgebra M]` context and expose no chosen predual. The two continuous-dual comparisons use
the weakest natural existing specified-predual boundary:

```lean
[NonUnitalCStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
[NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]
```

This matches the abstraction level of
`PositiveLinearMap.isNormalOnProjections_iff_mem_continuousDual`; a specified predual supplies
unitality internally.

## Proof architecture and reuse

The forward intrinsic bridge reuses the complete existing theorem

```lean
PositiveLinearMap.isNormalOnProjections_iff_mem_continuousDual
```

to obtain ultraweak continuity. The functional is transported to a positive continuous linear map
on `σ(M,P)`; `PositiveContinuousLinearMap.scottContinuous` then preserves every directed least
upper bound. `Ultraweak.ofUltraweakOrderIso` transports the result back to `M`.

For the converse, a directed family of projection-subtype elements is coerced into `M`.
`IsStarProjection.isLUB_coe_of_isLUB` identifies its projection-order least upper bound as the
ambient least upper bound, so Scott continuity immediately gives
`IsNormalOnProjections`. Restricting to nonnegative sets suffices because every star projection is
nonnegative.

Thus the source-facing Theorem 1.13.2 is a short equivalence chain:

```text
bounded directed-positive LUB preservation
  ↔ directed-positive LUB preservation
  ↔ normality on projections
  ↔ membership in the specified ultraweak continuous dual.
```

No part of the existing cutoff/Zorn/corner proof is duplicated.

## Library audit

The comparison used:

- Sak-AI baseline `d19b0d77f71931add5f925a66156208ba7232425`;
- pinned Mathlib `476ab284693e554a6b48c5f5210cb4fb5ae51252`;
- audited current Mathlib `be865aa50cc0364be66c3941a6dc0c845a2c2ceb`;
- read-only original LeanOA `cb811c1006ae78a0ff1d175253200e1859843370`.

Pinned and audited current Mathlib provide `ScottContinuous`, `ScottContinuousOn`, positive linear
maps, and Mathlib's existential `WStarAlgebra` class, but no operator-algebra normal-functional,
projection-normality, ultraweak-continuous-dual, or complete-additivity theorem. Original LeanOA
contains the earlier ultraweak LUB foundation but not the present normality characterization. The
new module is therefore a connective bridge over existing Sak-AI mathematics, not a replacement
foundation.

## Source consequences

The literal Definition 1.13.1 condition is now connected to the canonical Sak-AI predicate, and
the specified-predual equivalence gives the exact statement of Theorem 1.13.2 without changing its
positive-functional, arbitrary-directed-family, boundedness, supremum, or topology semantics.
Corollary 1.13.3 continues to reuse the existing predual-uniqueness API. The parallel
`Ultraweak.OrthogonalProjectionSum` module supplies the geometric part of Definition 1.13.4;
complete additivity remains a separate deferred workstream.

## Integrity

The focused module elaborates without placeholders. `#print axioms` for the principal declarations
reports only:

```text
propext
Classical.choice
Quot.sound
```

There are no custom axioms, `sorry`, `admit`, or opaque mathematical placeholders.
