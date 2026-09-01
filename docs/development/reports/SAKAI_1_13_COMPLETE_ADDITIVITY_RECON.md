# Sakai 1.13 complete-additivity reconnaissance

## Decision

```text
RECOMMENDED PRODUCTION STATUS: DEFER
```

The source semantics and the forward implication are now clear.  The converse is mathematically
credible, but it requires a genuine maximal-orthogonal-decomposition theorem and a chain-continuous
variant of the existing cutoff/Zorn characterization.  Publishing a permanent complete-additivity
predicate before those interfaces settle would be premature.

The kernel-checked scratch file is
[`Scratch/SakaiCompleteAdditivity.lean`](../../../Scratch/SakaiCompleteAdditivity.lean).

## Source semantics

Source: Sakai, *$C^*$-Algebras and $W^*$-Algebras*, printed p. 30, local PDF p. 42 at
`/Users/jonbannon/Desktop/ClaudeMath/SakaiBook_1971.pdf`.

### Definition 1.13.4

Sakai starts with an **arbitrary** index set `I` and a family `(e_alpha)_(alpha in I)` of mutually
orthogonal projections.  For each finite subset `J` of `I`, he sets

```text
P_J = sum over alpha in J of e_alpha.
```

The finite subsets are ordered by inclusion.  The resulting projection family is uniformly
bounded, increasing, and directed.  Sakai states that it converges ultraweakly to its least upper
bound and then strongly to the same projection.  He defines

```text
sum over alpha in I of e_alpha = lub_J P_J.
```

There is no countability or separability hypothesis.  The sum is not initially a sequence or an
ordinary countable series; it is the net of all finite partial sums.

Immediately after defining the projection sum, Sakai states that normality is equivalent to
complete additivity.  In the positive-functional context of 1.13.1--1.13.2, this means that for
every arbitrary mutually orthogonal projection family,

```text
phi (sum over alpha in I of e_alpha) = sum over alpha in I of phi (e_alpha).
```

This equivalence is prose attached to Definition 1.13.4, not a separately numbered theorem or a
second definition.

### Definition 1.13.5

Definition 1.13.5 does **not** define complete additivity.  It calls an arbitrary linear functional
on `M` normal when it is `sigma(M,M_*)`-continuous.  Positivity is not assumed in 1.13.5.  Thus the
section contains two related uses of “normal” which should remain distinct in Lean:

- positive normality from the order property in 1.13.1, characterized topologically in 1.13.2;
- arbitrary normal linear functionals from ultraweak continuity in 1.13.5.

## Scalar summation semantics

Sakai does not separately redefine the scalar sum on the right side of the complete-additivity
identity.  In context its source-faithful meaning is the unconditional sum of the nonnegative
scalars `phi (e_alpha)`, namely the limit, equivalently the least upper bound, of all finite scalar
partial sums.

Mathlib's `HasSum` has exactly this meaning by default:

```lean
HasSum f a
```

is convergence to `a` of the net

```lean
fun J : Finset I => ∑ i in J, f i
```

along the unconditional finite-subset summation filter.  Its index type is arbitrary.  It does not
silently replace the source family by a sequence.

For a positive functional and projections, every term is a nonnegative complex number with zero
imaginary part under Sak-AI's `ComplexOrder`.  Finite partial sums are monotone.  They are also
bounded by `phi 1`, since every finite orthogonal projection sum is at most `1`.  Consequently the
scalar family is summable even when the projection index type is uncountable.  As usual for a
summable family in `ℂ`, only countably many scalar terms can be nonzero; that is a consequence, not
an input restriction on `I` or on the projection family.

The following equivalence was kernel-checked for arbitrary `I`:

```lean
HasSum f a ↔
  IsLUB (Set.range (fun J : Finset I => ∑ i in J, f i)) a
```

under `∀ i, 0 ≤ f i`.  The proof uses:

- `Finset.sum_mono_set_of_nonneg`;
- `isLUB_of_tendsto_atTop`;
- `tendsto_atTop_isLUB`;
- Sak-AI's `Complex.instSupConvergenceClass`.

Thus the topological and order-theoretic readings of Sakai's scalar sum agree exactly here.

## Candidate Lean formulations

### `HasSum` -- recommended statement semantics

For one family, the source identity should have the shape

```lean
HasSum (fun i => phi (p i).1) (phi q.1)
```

where `q` is the projection-order LUB of the finite partial sums, equivalently the projection
`iSup` once the orthogonal-sum interface proves that identification.

Advantages:

- arbitrary index types;
- literally the finite-subset net used by the source;
- contains convergence and the value in one proposition;
- does not inherit `tsum`'s default value when summability is absent.

### Finite-partial-sum `IsLUB` -- equally faithful order interface

For positive scalar values, the following is equivalent and may be the better internal proof
interface:

```lean
IsLUB
  (Set.range (fun J : Finset I => ∑ i in J, phi (p i).1))
  (phi q.1)
```

It exposes Sakai's order semantics directly and composes immediately with
`PositiveLinearMap.IsNormalOnProjections`.

### `Summable` plus `tsum`

This is mathematically valid once summability is included or separately proved:

```lean
Summable (fun i => phi (p i).1) ∧
  ∑' i, phi (p i).1 = phi q.1
```

Mathlib's `tsum` also supports arbitrary index types and uses unconditional finite-subset
summation.  It is therefore not intrinsically countable.  However, bare equality with `tsum` is a
poor definition because `tsum` returns `0` when the family is not summable.  `HasSum` makes the
logical content explicit and should be preferred unless a generic orthogonal-value summability
theorem is already in the public API.

### `ENNReal` or `NNReal`

`ENNReal.tsum_eq_iSup_sum` gives a convenient total complete-lattice formula, but changing the
functional's scalar values from `ℂ` to `ℝ≥0∞` obscures the source statement and creates coercion
work.  `NNReal` avoids infinity but still requires a bundled conversion of every positive complex
value.  Neither should be the primary source-facing formulation.

## Family and universe shape

A provisional family-level statement can use

```lean
p : I → {p : M // IsStarProjection p}
Pairwise (fun i j => (p i).1 * (p j).1 = 0)
```

For star projections one product-zero equation gives the reverse equation by applying `star`.
The target projection should be the existing projection-lattice supremum or the finite-partial-sum
LUB supplied by the orthogonal-sum module.  No new projection type, sum object, or notation is
needed.

A global predicate which quantifies internally over `I : Type v` acquires a universe parameter
`v`.  Before publishing such a predicate, integration should decide whether to:

- expose family-level theorems polymorphic in `I`;
- use sets of projections and their subtype as the index type; or
- adopt an explicitly universe-parameterized predicate.

This is another reason not to publish the predicate during the reconnaissance wave.

## Forward implication: normal implies completely additive

The scratch theorem

```text
SakaiCompleteAdditivityScratch.normal_hasSum_of_partialSum_isLUB
```

accepts an explicit finite-partial-sum projection map

```lean
P : Finset I → {p : M // IsStarProjection p}
```

with only these hypotheses:

```lean
(P J).1 = ∑ i in J, (p i).1
Monotone P
IsLUB (Set.range P) q.
```

From `phi.IsNormalOnProjections`, Scott continuity sends the last LUB to the scalar LUB

```lean
IsLUB (Set.range (fun J => phi (P J).1)) (phi q.1).
```

The complex supremum-convergence instance turns this into convergence of the finite scalar partial
sums, and linearity identifies those sums with `sum (phi (p i))`.  The conclusion is the exact
arbitrary-index statement

```lean
HasSum (fun i => phi (p i).1) (phi q.1).
```

This direction is short and fully kernel-checked.  It needs no chosen predual, ultraweak topology,
spectral approximation, spectral integral, PVM, or polar decomposition.  Once the orthogonal-sum
workstream exports the three hypotheses above, this direction is ready for a bounded production
transaction.

## Converse: exact blocker

Complete additivity directly controls orthogonal finite-partial-sum nets.  The canonical existing
normality predicate is Scott continuity on **every nonempty directed set of projections**.  Passing
from the former to the latter is a real theorem about the complete projection lattice, not a
definitional simplification.

The source clue “from the proof of 1.13.2” is important.  Sakai's cutoff proof invokes Zorn and
therefore needs preservation of projection LUBs only for the chains appearing in the maximality
arguments.  It is enough to establish the following chain decomposition lemma.

### Minimal maximal-orthogonal-family lemma

Given a nonempty chain `c` of projections with LUB `q`, construct an arbitrary family `e : I →
Projection M` and its finite partial sums `E_J` such that:

1. the `e_i` are pairwise orthogonal;
2. `q` is the LUB of the `E_J`;
3. for every finite `J`, there is `r ∈ c` with `E_J ≤ r`.

Then complete additivity gives

```text
phi q = sum_i phi (e_i).
```

Every finite scalar partial sum is at most `phi r` for some `r ∈ c`, so `phi q` is the LUB of
`phi '' c`.  The scratch theorem

```text
SakaiCompleteAdditivityScratch.isLUB_apply_of_hasSum_of_finset_domination
```

kernel-checks precisely this final reduction.  The unresolved mathematics is the construction of
the orthogonal family, not the scalar limit argument.

### Expected construction

A promising source-faithful construction is a Zorn-maximal family of nonzero pairwise orthogonal
projections `e` such that:

- each `e` lies below some member of the chain;
- each `e` commutes with every member of the chain.

Finite subfamilies are dominated by one chain member because a finite subset of a chain has a
largest relevant bound.  Let `q_0` be the orthogonal sum of the maximal family.  The missing
commutation-closure lemma should show that `q_0` commutes with every chain member, using convergence
of finite partial sums and separate multiplication.  If `q_0 < q`, the LUB property supplies a
chain member `r` not below `q_0`.  Since `r` commutes with `q_0`, the defect

```text
r * (1 - q_0)
```

is a nonzero projection, is orthogonal to the maximal family, lies below `r`, and still commutes
with the chain.  This contradicts maximality.  Hence `q_0 = q`.

No matching complete-orthomodular-lattice or completely-additive-projection-measure theorem was
found in pinned Mathlib or Sak-AI.  Mathlib's cofinality library does not by itself provide this
operator-algebraic orthogonal decomposition.

## Route from chain continuity to canonical normality

The existing proof stack can likely be generalized without changing its public theorem:

- `NormalCutoff.exists_maximal_isUltraweakCutoff` uses normality only to close the cutoff property
  under the chains passed to Zorn;
- `NormalSelection.exists_nonzero_subprojection_lt_of_chain_lubs` applies the two functionals'
  LUB-preservation properties only to a chain;
- the rest of `NormalCharacterization` then proves ultraweak continuity;
- existing ultraweak-continuity-implies-normality yields full `IsNormalOnProjections`.

The smallest honest converse transaction is therefore:

```text
maximal orthogonal decomposition of a projection chain
  -> complete additivity preserves chain LUBs
  -> chain-continuous cutoff/Zorn characterization
  -> ultraweak continuity
  -> IsNormalOnProjections
  -> Sakai 1.13.1 via the source-normality bridge.
```

Trying to prove Scott continuity for arbitrary directed projection families directly is likely a
larger and less source-aligned local minimum.

## Spectral and polar-decomposition dependencies

### Forward direction

None.

### Converse through the proposed chain route

New dependencies:

- arbitrary orthogonal projection finite sums and their LUB;
- convergence of those partial sums;
- closure of commutation under that limit;
- Zorn maximality for the orthogonal family;
- chain-LUB variants of existing cutoff/selection helpers.

Existing analytic dependencies inherited from `NormalCharacterization`:

- Cauchy--Schwarz cutoff estimates;
- predual separation;
- real-rank-zero approximation of positive corner elements by finite positive combinations of
  projections;
- strong-to-ultraweak continuity.

The converse does **not** require:

- the unresolved Sakai 1.11 spectral integral or a PVM;
- a new spectral approximation of arbitrary positive elements;
- Sakai 1.12 element polar decomposition;
- polar decomposition of linear functionals from the next section.

An alternative direct proof from complete additivity to Sakai's all-positive directed condition
might invoke spectral approximation, but that is unnecessary if the project first reaches the
canonical projection-normality predicate and reuses the source-normality bridge.

## Kernel-checked scratch results

Direct command:

```sh
lake env lean Scratch/SakaiCompleteAdditivity.lean
```

Result: success.

Declarations checked:

```text
SakaiCompleteAdditivityScratch.hasSum_iff_isLUB_finsetSum_of_nonneg
SakaiCompleteAdditivityScratch.normal_hasSum_of_partialSum_isLUB
SakaiCompleteAdditivityScratch.isLUB_apply_of_hasSum_of_finset_domination
```

For each declaration, `#print axioms` reports only:

```text
[propext, Classical.choice, Quot.sound]
```

No custom axiom, `sorry`, `admit`, or equivalent placeholder occurs in the scratch file.

## Recommended next bounded transaction

1. Integrate the orthogonal finite-sum/LUB interface from the parallel projection workstream.
2. Promote only `normal implies complete additivity`, preferably first as a theorem for an explicit
   arbitrary projection family using `HasSum`.
3. In a separate transaction, prove the maximal orthogonal decomposition of a projection chain and
   the commutation-closure lemma.
4. Generalize the private/internal cutoff and selection proof boundary from full projection Scott
   continuity to chain-LUB preservation.
5. Only after the converse kernel-checks, decide whether a permanent complete-additivity predicate
   has earned public status.

Until steps 3--4 are complete:

```text
normal => completely additive: PROOF SHAPE KERNEL-CHECKED
completely additive => normal: DEFERRED WITH PRECISE BLOCKER
public complete-additivity predicate: DEFERRED
```
