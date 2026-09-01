# Sakai Section 1.13 source audit

Date: 2026-08-31

Baseline: `d19b0d77f71931add5f925a66156208ba7232425`

## Audit boundary

The source is Sakai, *$C^*$-Algebras and $W^*$-Algebras*, Section 1.13, inspected
directly in `/Users/jonbannon/Desktop/ClaudeMath/SakaiBook_1971.pdf`.  The section
is titled **Linear Functionals on a $W^*$-Algebra**.  It occupies printed
pp. 28--30 (PDF pp. 40--42) and ends before Section 1.14 on printed p. 31.

This audit confirms and sharpens the earlier cartography in
`SAKAI_SECTION_1_13_SCOPE.md`; it does not infer source semantics from the
existing Lean API.

## Numbered source items

| Item | Printed / PDF page | Exact mathematical content |
| --- | --- | --- |
| Definition 1.13.1 | 28 / 40 | A **positive linear functional** `phi` is normal when `phi (lub x_alpha) = lub (phi (x_alpha))` for every **uniformly bounded increasing directed set** of positive elements. |
| Theorem 1.13.2 | statement 28 / 40; proof 29--30 / 41--42 | For a positive linear functional, source normality is equivalent to continuity for `sigma(M,M_*)`. |
| Corollary 1.13.3 | 30 / 42 | The Banach predual is unique after the candidate preduals are canonically embedded in the norm dual. |
| Definition 1.13.4 | 30 / 42 | For an arbitrary mutually orthogonal projection family indexed by a set `I`, its sum is the LUB of its finite partial sums.  Those partial sums converge ultraweakly and strongly to the LUB.  The following paragraph states that positive-functional normality is equivalent to complete additivity. |
| Definition 1.13.5 | 30 / 42 | An arbitrary linear functional continuous for `sigma(M,M_*)` is called a normal linear functional. |

There is no numbered theorem after Definition 1.13.5.  The concluding remarks
attribute Theorem 1.13.2 to Dixmier and discuss uniqueness of a Banach predual as
a Banach-space phenomenon.

## Directed-positive semantics

Definition 1.13.1 uses a genuinely arbitrary directed set, not a sequence.  Its
condition is an equality of order-theoretic least upper bounds, not a separately
stated topological convergence condition.  The family is positive and increasing,
and "uniformly bounded" is norm boundedness in the ambient $C^*$-algebra.

For the Lean bridge, the literal family class is therefore

```lean
{s : Set M | Bornology.IsBounded s ∧ ∀ x ∈ s, 0 ≤ x}.
```

Mathlib's `ScottContinuousOn` asks a map to preserve every supplied `IsLUB` for
sets in this class.  This is the right existing order notion; no new normality
predicate is required.  The boundedness clause is redundant once a nonnegative
set is supplied with an `IsLUB`: if `a` is its LUB then every member lies in the
order interval `[0,a]`, hence the set is norm bounded.  The production bridge
should nevertheless retain a theorem with the printed boundedness clause and
record the equivalent unbounded-looking `IsLUB` formulation separately.

Positivity makes the scalar values monotone.  Consequently preservation of the
LUB also yields convergence of the canonical scalar net, but that convergence is
a consequence rather than the source definition.

## Projection-family and complete-additivity semantics

Definition 1.13.4 fixes an arbitrary index set `I` and a mutually orthogonal
family `(e_alpha)`.  For each finite subset `J`, Sakai puts

```text
P_J = sum_{alpha in J} e_alpha.
```

Inclusion of finite subsets orders these partial sums into a uniformly bounded
increasing directed net.  Sakai first obtains convergence in `sigma(M,M_*)`, then
uses a positive-functional estimate to obtain convergence in the intrinsic strong
topology `s(M,M_*)`.  The LUB is a projection and is defined to be
`sum_{alpha in I} e_alpha`.

There is no countability hypothesis.  In Lean the faithful index is therefore
`Finset I` with its inclusion order and `atTop`, for arbitrary `I`.  Ordinary
`tsum` is not the definition of the operator sum.

The subsequent complete-additivity statement is also for every arbitrary
mutually orthogonal family:

```text
phi (sum_alpha e_alpha) = sum_alpha phi(e_alpha).
```

The scalar right-hand side is naturally the limit, equivalently the LUB, of the
finite scalar subsums.  Mathlib's `HasSum` has precisely this arbitrary-index
finite-subset-net semantics.  A bare equality involving `tsum` would be unsafe as
a predicate because `tsum` has a default value when summability is absent.

## Proof dependencies in the source

For ultraweak continuity implying Definition 1.13.1, Sakai cites 1.7.4.  For the
reverse direction of Theorem 1.13.2, he uses:

- directed LUBs of projections (forward-referencing 1.13.4);
- Cauchy--Schwarz estimates for positive functionals;
- maximal projections and a second maximal subprojection argument;
- approximation of positive corner elements by finite positive combinations of
  projections in a maximal commutative $C^*$-subalgebra with Stonean spectrum;
- the strong-to-ultraweak continuity result 1.8.10.

These are already represented by Sak-AI's `NormalCutoff`, `NormalSelection`,
`NormalCharacterization`, real-rank-zero, projection-lattice, and topology APIs.
The present work must connect Definition 1.13.1 to that stack, not replay it.

The proof of Corollary 1.13.3 identifies the canonically embedded predual with the
norm-closed span of positive normal functionals.  Sak-AI already supplies the
Lean-correct equality of represented continuous-dual subspaces and the canonical
pairing-preserving equivalence between distinct predual types.

Sakai says that the complete-additivity equivalence follows easily from the proof
of 1.13.2, but does not spell out the converse.  The forward implication follows
from finite partial sums and projection normality.  The converse still needs a
proof that preservation of arbitrary orthogonal joins controls the directed
projection LUBs consumed by the cutoff argument; the source does not license
silently weakening this to sequences.

## Polar decomposition and topology boundary

Section 1.13 does not invoke the element polar decomposition of Section 1.12 in
the positive-functional normality or projection-sum arguments.  Later passage
from positive to arbitrary normal functionals uses the existing functional
decomposition/predual machinery, not a reason to rebuild element polar
decomposition here.

The topologies are unambiguous in this section:

| Source notation | Sak-AI object | Use |
| --- | --- | --- |
| `sigma(M,M_*)` | `Ultraweak M P` | Theorem 1.13.2 and first projection-net convergence |
| `s(M,M_*)` | `Ultraweak.Strong M P` | strong convergence of finite projection sums |
| norm boundedness | ambient norm bornology | family hypothesis in Definition 1.13.1 |

No new topology, chosen-predual redesign, spectral integral, or PVM is required.

## Source-fidelity decisions for this wave

- Preserve arbitrary directed and arbitrary index-type quantifiers.
- Express source normality through existing `ScottContinuousOn`, with the literal
  bounded/nonnegative family class and a proved redundancy bridge.
- Keep `PositiveLinearMap.IsNormalOnProjections` authoritative.
- Represent operator sums by projection LUBs of `Finset` partial sums, not `tsum`.
- Keep the complete-additivity predicate and converse out of production until the
  missing arbitrary-directed projection argument has been reviewed.
