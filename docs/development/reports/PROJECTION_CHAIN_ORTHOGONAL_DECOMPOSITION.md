# Projection-chain orthogonal decomposition

## Scope and source status

This report records the projection-chain decomposition used in the converse direction of the
complete-additivity characterization surrounding Sakai Definition 1.13.4.

Source: Sakai, *$C^*$-Algebras and $W^*$-Algebras*, printed p. 30 (local scan p. 42), inspected
directly at `/Users/jonbannon/Desktop/ClaudeMath/SakaiBook_1971.pdf`.

Sakai defines the sum of an arbitrary mutually orthogonal projection family as the least upper
bound of its finite partial sums. He then says tersely that, “from the proof of 1.13.2,” normality
is equivalent to complete additivity. He does **not** print a projection-chain decomposition,
maximal orthogonal-family argument, or detailed converse proof on p. 30. Consequently, the theorem
below is not presented as a verbatim formalization of a displayed source lemma. It is a faithful
reconstruction of the maximality architecture referenced by Sakai, designed to supply the exact
chain-LUB input isolated by the prior complete-additivity reconnaissance.

The reconstruction preserves the source's arbitrary-cardinality setting. It does not replace a
chain by a sequence and does not impose countability or separability.

## Reuse audit and design boundary

Before introducing any new foundational theorem or proof pattern, search Mathlib, search the original LeanOA repository, and search the current Sak-AI repository for an existing theorem, definition, abstraction, or argument that already supplies the needed mathematics; reuse it where mathematically faithful, preserve architectural continuity with the APIs already built, and generalize only when that genuinely improves portability or reuse rather than duplicating local infrastructure.

The audit found no existing projection-chain theorem that supplies an orthogonal family together
with finite domination and recovery of the chain LUB. The implementation reuses:

- Mathlib's `zorn_subset_nonempty`, `Set.Pairwise`, `IsChain.total`, and ordinary `Finset`
  induction;
- Mathlib's star-projection complement, product, order, and commutation lemmas;
- Sak-AI's canonical complete lattice on `{p : M // IsStarProjection p}`;
- `IsStarProjection.orthogonalFinsetSum`, its monotonicity, and its projection LUB theorem;
- the generic `IsStarProjection.commute_of_isLUB`, which passes commutation with a fixed element
  through a nonempty directed projection LUB using separate ultraweak continuity.

No chain type, orthogonal-family structure, infinite-sum notation, projection type, or competing
commutation theorem was introduced. The maximal-family predicate and its Zorn proof are private
implementation details.

## Maximal family

Let `c` be a nonempty chain of projections and let `q` be its least upper bound. A projection `p`
is admissible for the construction when:

1. `p` is nonzero;
2. `p ≤ r` for some `r ∈ c`;
3. `p` commutes with every member of `c`.

A set of projections is an admissible orthogonal family when all its members are admissible and
distinct members multiply to zero. The empty set is such a family. The union of any inclusion
chain of such families is again admissible and pairwise orthogonal: two elements of the union lie
in two comparable members of the inclusion chain, hence lie together in one of them.

`zorn_subset_nonempty` therefore gives a maximal admissible orthogonal set `s`. The construction
does not expose this maximality predicate publicly; it is proof scaffolding rather than a stable
consumer abstraction.

## Index type and orthogonality

The orthogonal family is indexed by the subtype `s` itself:

```lean
fun p : s ↦ p.1
```

Thus its index type is arbitrary and has exactly the cardinality of the chosen maximal set. The
set-level pairwise-orthogonality proof is converted to the function-level interface expected by
`OrthogonalProjectionSum`:

```lean
horth : Pairwise fun p r : s ↦ p.1.1 * r.1.1 = 0
```

No enumeration, `Countable`, `Encodable`, `Fintype`, `Summable`, or `tsum` is involved.

## Finite domination

Each member of `s` lies below some member of `c`. For a finite subset `t : Finset s`, finite
induction and total comparability of `c` select one `r ∈ c` dominating the finitely many chosen
chain witnesses. The reusable projection lemma

```text
IsStarProjection.orthogonalFinsetSum_le_of_forall_le
```

then turns pointwise domination of the summands into domination of their orthogonal finite sum:

```lean
∃ r ∈ c,
  IsStarProjection.orthogonalFinsetSum (fun p : s ↦ p.1) horth t ≤ r
```

The helper is public because it is a natural missing companion to the existing member-below-sum
and sum-monotonicity API. Its exact generality is:

```lean
theorem IsStarProjection.orthogonalFinsetSum_le_of_forall_le
    {M I : Type*} [NonUnitalCStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
    (p : I → {q : M // IsStarProjection q})
    (horth : Pairwise fun i j ↦ (p i).1 * (p j).1 = 0)
    {s : Finset I} {r : {q : M // IsStarProjection q}}
    (h : ∀ i ∈ s, p i ≤ r) :
    IsStarProjection.orthogonalFinsetSum p horth s ≤ r
```

The pure finite-chain selection induction remains private because it is short proof scaffolding
and does not yet justify a separate Sak-AI order API.

## Commutation of the orthogonal LUB

Write

```lean
q₀ = ⨆ p : s, p.1
```

Every finite partial sum commutes with every `r ∈ c`, since each summand does and multiplication
distributes over finite sums. The finite partial sums form a nonempty directed family and have
`q₀` as their LUB by the existing orthogonal-projection-sum API. The proof applies

```text
IsStarProjection.commute_of_isLUB
```

to conclude `Commute q₀.1 r.1`. That generic theorem uses the selected predual only internally to
obtain ultraweak convergence and passes equality to the limit by separate ultraweak continuity of
left and right multiplication. The projection-chain module does not duplicate this analytic
argument and does not expose a narrower orthogonal-family commutation theorem.

## Recovery of the chain LUB

Finite domination first gives `q₀ ≤ q`: every member of the orthogonal family lies below a chain
member, and every chain member lies below `q`.

For the converse, fix `r ∈ c` and suppose `r ≰ q₀`. Since `r` commutes with `q₀`, define the defect

```text
d = r * (1 - q₀).
```

The projection calculus gives:

- `d` is a projection;
- `d ≠ 0`, because `d = 0` would imply `r ≤ q₀`;
- `d ≤ r`;
- `d` commutes with every chain member: chain members commute with one another, and `q₀` commutes
  with the chain;
- `d` is orthogonal to every member of `s`, since every such member lies below `q₀`.

Thus inserting `d` produces a strictly larger admissible orthogonal family, contradicting the
Zorn maximality of `s`. Hence every `r ∈ c` lies below `q₀`. The least-upper-bound property of `q`
gives `q ≤ q₀`, and therefore

```lean
(⨆ p : s, p.1) = q.
```

This is the exact recovery statement needed to apply complete additivity to the constructed
orthogonal family while comparing its finite scalar subsums with values on the original chain.

## Public declaration

The production module is:

```text
LeanOA.Ultraweak.ProjectionChain
```

Its single public decomposition theorem is deliberately consumer-facing:

```lean
theorem IsChain.exists_orthogonal_projection_family
    {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
    [WStarAlgebra M]
    {c : Set {p : M // IsStarProjection p}} (hc : IsChain (· ≤ ·) c)
    (hcne : c.Nonempty) {q : {p : M // IsStarProjection p}} (hcq : IsLUB c q) :
    ∃ s : Set {p : M // IsStarProjection p},
      ∃ horth : Pairwise fun p r : s ↦ p.1.1 * r.1.1 = 0,
        (∀ t : Finset s, ∃ r ∈ c,
          IsStarProjection.orthogonalFinsetSum (fun p : s ↦ p.1) horth t ≤ r) ∧
        (⨆ p : s, p.1) = q
```

The result exposes only the arbitrary subtype-indexed family, pairwise orthogonality, finite
domination, and LUB equality. Nonzeroness, chain commutation, admissibility, maximality, and the
defect construction remain private because downstream complete-additivity arguments do not need
them as hypotheses.

## Generality and dependency boundary

The finite-sum domination helper needs only a nonunital $C^*$-algebra with the projection order.
The decomposition theorem is stated for a $W^*$-algebra because it uses the canonical complete
lattice of projections and the directed-LUB commutation theorem obtained from a predual. The
public theorem does not expose a chosen predual: `WStarAlgebra.predual M` is used only inside the
proof.

The family and chain are arbitrary sets in the ambient universe. No spectral integral, PVM,
measurable functional calculus, strong topology, or countability assumption enters the theorem.

## Validation and logical integrity

The focused builds and direct elaboration succeeded:

```text
lake build LeanOA.Ultraweak.OrthogonalProjectionSum
lake build LeanOA.Ultraweak.ProjectionChain
lake env lean LeanOA/Ultraweak/ProjectionChain.lean
lake build LeanOA
```

`#print axioms` reports for both
`IsStarProjection.orthogonalFinsetSum_le_of_forall_le` and
`IsChain.exists_orthogonal_projection_family` only:

```text
[propext, Classical.choice, Quot.sound]
```

`Classical.choice` is expected from Zorn's lemma and the selected predual. No custom axiom,
`sorry`, `admit`, opaque assumption, or other mathematical placeholder is present.
