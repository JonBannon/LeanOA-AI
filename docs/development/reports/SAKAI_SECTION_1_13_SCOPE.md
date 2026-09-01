# Sakai Section 1.13 scope

## Audit boundary

Source: Sakai, *$C^*$-Algebras and $W^*$-Algebras*, Section 1.13, inspected directly in the local
scan at `/Users/jonbannon/Desktop/ClaudeMath/SakaiBook_1971.pdf`.

Completion update (2026-09-01): all numbered items and substantive assertions scoped below are now
source-formalized. The first wave supplied the source-normality and orthogonal-sum APIs; the second
supplied projection-chain decomposition and complete additivity iff normality. This report remains
the pre-production scope record; see `SAKAI_1_13_COMPLETE_ADDITIVITY.md` for the closeout.

Section 1.13 is titled **Linear Functionals on a $W^*$-Algebra**. It begins on printed p. 28
(local PDF p. 40), continues through printed pp. 29--30 (local PDF pp. 41--42), and ends before
Section 1.14, **Polar Decomposition of Linear Functionals on a $W^*$-Algebra**, which begins on
printed p. 31 (local PDF p. 43). Thus Section 1.13 is the actual section immediately following
Theorem 1.12.1.

The audit compared the source with:

- Sak-AI at baseline `9ef19a9f13080503ee16951d32889e74ce32a53b`;
- pinned Mathlib at `476ab284693e554a6b48c5f5210cb4fb5ae51252`;
- current Mathlib at `be865aa50cc0364be66c3941a6dc0c845a2c2ceb` (audited 2026-08-31);
- the read-only original LeanOA at `cb811c1006ae78a0ff1d175253200e1859843370`.

## Exact numbered content

| Source item | Printed / PDF page | Content |
| --- | --- | --- |
| 1.13.1, Definition | 28 / 40 | A positive linear functional `phi` on a $W^*$-algebra is **normal** when it preserves the least upper bound of every uniformly bounded increasing directed family of positive elements. |
| 1.13.2, Theorem | statement 28 / 40; proof 29--30 / 41--42 | A positive linear functional is normal if and only if it is continuous for `sigma(M,M_*)`. |
| 1.13.3, Corollary | 30 / 42 | A $W^*$-algebra has a unique Banach predual, where uniqueness means equality after the two preduals are canonically embedded in the norm dual. |
| 1.13.4, Definition | 30 / 42 | For a mutually orthogonal family of projections, define its sum as the least upper bound of its finite partial sums. The source proves ultraweak and strong convergence of those partial sums and states that normality is equivalent to complete additivity on such families. |
| 1.13.5, Definition | 30 / 42 | A `sigma(M,M_*)`-continuous linear functional is called a normal linear functional. |

There are no further numbered items in the section. The concluding remarks attribute Theorem
1.13.2 to Dixmier and discuss uniqueness of a Banach predual as a Banach-space phenomenon; they do
not add another mathematical declaration.

## Source proof reconstruction

For Theorem 1.13.2, Sakai cites 1.7.4 for ultraweak continuity implying normality. For the reverse
implication, he first considers projections `p_alpha` such that the cutoff functional

```text
x |-> phi (x * p_alpha)
```

is ultraweakly continuous. If `p` is their least upper bound, Cauchy--Schwarz gives, uniformly on
the closed unit ball,

```text
|phi (x * (p - p_alpha))|
  <= phi(1)^(1/2) * phi(p - p_alpha)^(1/2).
```

Normality makes the right-hand side tend to zero. The ultraweakly continuous cutoffs are therefore
closed under directed projection suprema, and Zorn's lemma supplies a maximal such projection
`p_0`.

If `p_0` is not one, an ultraweakly continuous positive functional `psi` is chosen with
`phi(1 - p_0) < psi(1 - p_0)`. A second maximality argument produces a nonzero projection
`p_1 <= 1 - p_0` on whose nonzero subprojections `phi < psi`. Sakai extends this inequality from
projections to positive elements of the corner `p_1 M p_1` by using a maximal commutative
$C^*$-subalgebra with Stonean spectrum and uniform approximation by finite positive linear
combinations of projections. Cauchy--Schwarz then shows that the cutoff at `p_0 + p_1` is strongly
continuous and hence ultraweakly continuous by 1.8.10, contradicting maximality. Thus `p_0 = 1`.

After the theorem, Sakai identifies the predual with the norm-closed linear span of the positive
normal functionals. Since normality is characterized by the intrinsic order property, two
canonically embedded preduals coincide, yielding 1.13.3.

For 1.13.4, a finite subset `J` of the index type determines the partial sum `P_J`. Inclusion of
finite subsets makes these partial sums an increasing, uniformly bounded directed family. The
source first obtains ultraweak convergence to their least upper bound. A positive-functional
estimate upgrades this to convergence in `s(M,M_*)`; 1.8.12 then identifies the limit as a
projection. This least upper bound is declared to be the sum of the orthogonal family.

## Textbook order versus logical dependency order

The printed order is:

```text
normal positive functional (1.13.1)
  -> normal iff ultraweakly continuous (1.13.2)
  -> unique predual (1.13.3)
  -> arbitrary orthogonal projection sums (1.13.4)
  -> normal linear functional terminology (1.13.5).
```

The source proof itself forward-references 1.13.4 for a projection-supremum fact. A Lean-friendly
logical order is therefore:

```text
projection lattice and directed projection convergence
  -> finite partial sums of an orthogonal projection family
  -> source normality on positive directed families
  -> comparison with normality on projections
  -> Theorem 1.13.2 via the existing cutoff/Zorn theorem
  -> Corollary 1.13.3
  -> complete-additivity equivalence
  -> source terminology of 1.13.5.
```

This reordering changes no source statement. It only places the projection fact used by the proof
before its first consumer.

## Sak-AI overlap

Section 1.13 is not a fresh theorem cluster. Much of its difficult mathematics is already present
and publicly documented.

### Normality characterization

`LeanOA.Mathlib.Analysis.CStarAlgebra.PositiveLinearMap` defines

```text
PositiveLinearMap.IsNormalOnProjections
```

as Scott continuity of the induced map on the subtype of star projections. This definition is
purely order-theoretic and has no topological or $C^*$-algebra assumptions.

The following production modules implement Sakai's hard argument:

- `LeanOA.Ultraweak.Normal` proves that a positive functional represented by a specified predual
  is normal on projections;
- `LeanOA.Ultraweak.NormalCutoff` proves closure of the cutoff property under directed projection
  suprema and obtains a maximal cutoff projection;
- `LeanOA.Ultraweak.NormalSelection` formalizes the nonzero-subprojection selection argument;
- `LeanOA.Ultraweak.NormalCharacterization` proves

  ```text
  PositiveLinearMap.isNormalOnProjections_iff_mem_continuousDual.
  ```

The last theorem is stated for a nonunital $C^*$-algebra with a specified complete Banach predual,
so its abstraction boundary is more general than Sakai's unital $W^*$-algebra statement. Its proof
uses the existing corner predual, real-rank-zero approximation, strong topology, and separate
multiplication APIs rather than duplicating them.

The Verso chapter `SakAIDocs.Chapters.Normality` already presents this theorem and its source proof
structure; the current closeout adds an explicit caveat that the all-positive source bridge is
pending. A future Section 1.13 closeout must revise that chapter in place rather than create a
parallel public account.

### Unique predual

`LeanOA.Ultraweak.PredualUniqueness` already provides:

```text
Ultraweak.continuousDual_eq
Predual.equiv
Predual.equiv_apply_duality
Predual.equiv_eq_of_apply_duality_eq.
```

Equality of the two embedded continuous-dual subspaces is the direct Lean counterpart of Sakai's
canonical equality statement. The pairing-preserving linear isometric equivalence is the
type-correct strengthening needed when the preduals are distinct Lean types. This is an existing
GREEN result, not work to repeat. Its proof uses the already formalized polar decomposition of
ultraweakly continuous functionals.

### Projection least upper bounds and convergence

The analytic and order-theoretic backbone of 1.13.4 is already supplied by:

```text
IsStarProjection.instCompleteLatticeSubtypeOfWStarAlgebra
IsStarProjection.isLUB_coe_sSup
IsStarProjection.tendsto_toUltraweak_of_isLUB
IsStarProjection.tendsto_toUltraweak_sSup
Ultraweak.Strong.tendsto_toStrong_of_isLUB.
```

Mathlib's binary `IsStarProjection.add` supplies the algebraic induction step for finite sums of
orthogonal projections. What is absent is the exact family-level finite-partial-sum package, not a
projection lattice or a new strong topology.

### Normal linear functionals

`Ultraweak.continuousDual`, together with
`Ultraweak.mem_continuousDual_iff_continuous_ultraweak` and the predual factorization theorems,
already represents the mathematical object named in 1.13.5. A source-facing declaration or Verso
link may be useful, but no second functional type is justified.

## Mathlib and original LeanOA overlap

Pinned and current Mathlib both provide the reusable lower layers:

- `ScottContinuous` and `ScottContinuousOn`;
- positive linear maps and their monotonicity;
- star-projection algebra, including addition of orthogonal projections;
- generic finite sets, finite sums, directed orders, and least-upper-bound predicates;
- Banach--Alaoglu and the standard topological/filter infrastructure.

Both revisions also define `WStarAlgebra M` in
`Mathlib.Analysis.VonNeumannAlgebra.Basic`. This is a proposition-valued class whose sole
`exists_predual` field asserts the existence of a Banach space `X` and a nonempty conjugate-linear
isometric equivalence `StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M`. The same file defines the bundled concrete
double-commutant object `VonNeumannAlgebra H`. The file is unchanged between the pinned and current
commits. This is genuine foundational and naming overlap, so a future upstreaming pass must relate
Sak-AI's specified-predual hypotheses to Mathlib's existential `WStarAlgebra` class rather than
introduce another abstract $W^*$-algebra class.

That Mathlib declaration does not choose a predual and does not supply its pairing, the induced
ultraweak topology, normal positive functionals, or a uniqueness theorem. A targeted search of the
2026-08-31 current checkout found no `IsNormalOnProjections`, arbitrary orthogonal-projection-sum
or convergence API, or complete-additivity theorem. The relevant generic APIs remain
`ScottContinuous`/`ScottContinuousOn`, binary `IsStarProjection.add`, and ordinary finite-set and
least-upper-bound machinery. `Order.IsNormal` in current Mathlib concerns strictly monotone
continuous functions between well-orders and is unrelated to operator-algebra normality. Thus
current Mathlib still does not replace the existing Sak-AI normality stack or close any of the
three Section 1.13 fidelity gaps identified below.

The read-only original LeanOA contains the early specified-predual, ultraweak-topology,
`ComplexOrder`, and `Ultraweak.LUB` foundations. It does not contain the current `Dual`, `Normal`,
`NormalCutoff`, `NormalSelection`, `NormalCharacterization`, `ProjectionLattice`,
`StrongProjection`, or `PredualUniqueness` modules. The Section 1.13 theorem stack is therefore
current Sak-AI work built on, rather than duplicated from, the original repository.

## Source-fidelity gaps

### 1.13.1: positive-directed normality

Sakai quantifies over uniformly bounded increasing directed families of all positive elements.
The current permanent predicate quantifies over directed families of projections. These notions
are equivalent in the present $W^*$-algebra setting, but the explicit equivalence was not found in
the audited library.

Consequently, the mathematical core of 1.13.2 is kernel-proved, but exact certification of the
source wording should first add a bridge from Sakai's positive-family condition to
`IsNormalOnProjections`. This is a statement-fidelity gap, not a defect in the existing hard proof.

Do not create a second permanent notion of normality casually. Architecture must first choose
between a full `ScottContinuous` formulation and a source-exact positive-family restriction using
`ScottContinuousOn` or an explicit `IsLUB` predicate. A safe public result should compare the
chosen source-facing property with the established projection predicate.

### 1.13.4: orthogonal sums

No exact theorem was found which starts with an arbitrary pairwise orthogonal projection family,
constructs its finite partial sums, identifies their least upper bound with the lattice supremum,
and records both ultraweak and strong convergence. The existing lattice/convergence results make
this a bounded assembly task.

Sakai's sum is an uncountable directed supremum of finite partial sums. It must not silently be
identified with Mathlib's ordinary `tsum`, whose interface and summability semantics are different.
Prefer the existing projection `iSup`/`sSup` and a named finite-partial-sum convergence theorem;
introduce new notation only if a downstream consumer justifies it.

### Complete additivity

No complete-additivity predicate or equivalence with normality was found. The implication from
normality to preservation of an orthogonal-family sum should be short after the finite-partial-sum
API exists. The converse may require a maximal orthogonal-family or related decomposition
argument; it should not be advertised as routine before a scratch proof identifies the exact
dependency.

For an arbitrary index type, scalar complete additivity should initially be expressed through the
least upper bound of finite scalar partial sums, not through `tsum` without a countability
hypothesis.

## Coverage classification

| Item | Status after audit | Reason |
| --- | --- | --- |
| 1.13.1 | SOURCE-FORMALIZED | The exact bounded positive-directed condition is equivalent to canonical projection normality. |
| 1.13.2 | SOURCE-FORMALIZED | Normality is equivalent to ultraweak continuous-dual membership through the existing cutoff/Zorn proof. |
| 1.13.3 | SOURCE-FORMALIZED IN LEAN-CORRECT FORM | Equality of embedded continuous duals and the canonical pairing-preserving predual equivalence are public. |
| 1.13.4 | SOURCE-FORMALIZED | Arbitrary orthogonal finite sums, LUB and convergence, plus complete additivity iff normality, are public. |
| 1.13.5 | SOURCE-FORMALIZED | `Ultraweak.continuousDual` and the normality characterizations represent the source definition. |

Section 1.13 is complete. Its implementation reuses the stable normality and predual-uniqueness
mathematics rather than rebuilding the section wholesale.

## Dependency map

```text
Mathlib Scott continuity + positive linear maps
        +
original/current Ultraweak.LUB and order-closed topology
        +
ProjectionLattice + StrongProjection
        |
        +--> source positive-directed normality bridge
        |       |
        |       +--> existing IsNormalOnProjections
        |               |
        |               +--> existing NormalCutoff / NormalSelection
        |                       |
        |                       +--> existing NormalCharacterization
        |                               |
        |                               +--> exact source-facing 1.13.2
        |                                       |
        |                                       +--> existing PredualUniqueness (1.13.3)
        |
        +--> pairwise orthogonal family
                |
                +--> finite partial sums are projections and directed
                        |
                        +--> projection iSup/sSup
                                |
                                +--> ultraweak and strong convergence (1.13.4)
                                        |
source normality bridge + orthogonal-sum convergence
        |
        +--> normality implies complete additivity
                |
                +--> converse, after bounded scratch validation
```

No dependency on the unresolved Section 1.11 integral/PVM boundary is present.

## Recommended bounded workstreams

All workstreams are governed by the following requirement:

> **Read and obey `docs/development/SAKAI_DESIGN_CONTRACT.md` and the authoritative Sak-AI specifications it references. These requirements govern this workstream. Do not introduce designs inconsistent with them.**

The lead retains ownership of umbrella imports, coordination files, Verso integration, and final
API naming. Workers must not edit those shared files.

### Workstream A -- source normality bridge

- **Objective:** choose a source-faithful positive-directed normality formulation and prove its
  equivalence with `PositiveLinearMap.IsNormalOnProjections`; derive the exact 1.13.2 statement by
  reusing `isNormalOnProjections_iff_mem_continuousDual`.
- **Dependencies:** `PositiveLinearMap.IsNormalOnProjections`, `Ultraweak.LUB`,
  `PositiveContinuousLinearMap.scottContinuous`, and `Ultraweak.NormalCharacterization`.
- **Owned production surface:** one new narrow bridge module and one workstream report. The exact
  module and declaration names must be frozen by architecture before dispatch.
- **API stability:** YELLOW until the full-Scott-versus-positive-family choice is resolved; GREEN
  is plausible after independent source/API review.
- **Mathlib overlap:** reuse `ScottContinuous`/`ScottContinuousOn`; introduce no local order theory.
- **Collision constraint:** do not edit the existing `Normal`, `NormalCutoff`, `NormalSelection`, or
  `NormalCharacterization` proofs. Do not add a competing normal-functional type.
- **Parallel safety:** safe to run beside Workstream B once the source-facing predicate signature
  is centrally fixed.

### Workstream B -- orthogonal projection finite-sum net

- **Objective:** for an arbitrary pairwise orthogonal projection family, prove that finite partial
  sums are projections, form an increasing directed net, have lattice supremum `iSup`/`sSup`, and
  converge to it both ultraweakly and strongly.
- **Dependencies:** Mathlib `IsStarProjection.add`, Sak-AI `ProjectionLattice`, and
  `StrongProjection`.
- **Owned production surface:** one new orthogonal-projection-sum module and one workstream report.
- **API stability:** GREEN theorem layer if it uses the existing projection lattice and exposes no
  new foundational sum object.
- **Mathlib overlap:** isolate a generic finite-sum helper only if its weakest natural statement is
  independently recognizable; otherwise keep induction proof-local.
- **Collision constraint:** consume but do not edit `ProjectionLattice`, `StrongProjection`, or the
  shared mirrored projection module. Do not introduce `tsum` semantics or new global notation.
- **Parallel safety:** independent of Workstream A and safe to run concurrently in a separate new
  module.

### Workstream C -- complete-additivity converse reconnaissance

- **Objective:** test the exact arbitrary-index finite-subset formulation of complete additivity;
  prove the easy normal-to-completely-additive direction if possible locally, and determine the
  precise maximal-orthogonal-family lemma needed for the converse.
- **Dependencies:** explicit current projection-normality and projection-LUB hypotheses. It must not
  assume unintegrated declarations from Workstreams A or B.
- **Owned surface:** scratch Lean and a private/read-only report only during the parallel wave.
- **API stability:** RED for production until the converse and uncountable-sum semantics are
  reviewed; no public predicate or notation may be introduced by this stream.
- **Mathlib overlap:** use `Finset`, `IsLUB`, `ScottContinuous`, and Zorn/maximality machinery where
  applicable.
- **Collision constraint:** no production edits, no Verso edits, and no edits to A or B's modules.
- **Parallel safety:** safe beside A and B precisely because it remains scratch-only and states all
  provisional assumptions explicitly.

After A and B are reviewed, the lead can integrate the normal-to-complete-additivity implication.
The converse should become a later bounded production task only if Workstream C establishes a
clean dependency route. Final Section 1.13 Verso work should update the existing Normality chapter
and add the orthogonal-sum material without duplicating its current theorem nodes.

## Recommended next checkpoint

Run Workstreams A and B in parallel with C as scratch reconnaissance. The immediate production
checkpoint is:

```text
exact source normality bridge
  +
source-faithful orthogonal projection finite-sum convergence.
```

This checkpoint closes the literal-definition gap in 1.13.1 and the geometric portion of 1.13.4
while reusing the already complete proofs of 1.13.2 and 1.13.3. It is a Section 1.13
source-fidelity/orthogonal-sum closeout, not a restart of the section.
