# Mathlib spectral/integration audit

Status: architectural evidence only; no foundational decision is made here.

> **Source correction (2026-08-30).** This earlier implementation audit misread Latin `s` as
> Greek `σ` in Sakai's scan. Theorem 1.11.3 states the strong `s(M,M_*)` topology. The named
> ultraweak limits recommended here remain valid consequences of norm convergence, but they are
> not the exact source topology and do not certify the undefined integral semantics.

Workstream: `MATHLIB_SPECTRAL_AUDIT`

Questions addressed: `IQ-001`, `IQ-002`

Audit date: 2026-08-30

## Executive finding

The shortest honest route from Sak-AI's present finite spectral sums to the integral clause of
Sakai 1.11.3 is **not** to introduce an operator-valued measure immediately.  The existing Sak-AI
estimates already prove norm convergence, hence both strong and ultraweak convergence, of lower
and upper sums for the identity integrand. A small theorem-level interface may expose useful
limits without prematurely choosing a projection-valued-measure or integration foundation. Sakai's
exact integral semantics require more than naming the ultraweak consequence.

Mathlib's `MeasureTheory.VectorMeasure` has an important but limited fit:

- its *measure structure* is topology-parametric, so in principle it can state countable additivity
  in Sak-AI's `Ultraweak` topology;
- its *integration API* is normed and defined through total variation, so it does not provide the
  strong-topology Radon--Stieltjes integral required by the source;
- a general spectral projection family is not norm-countably additive and need not have bounded
  norm variation (infinitely many nonzero orthogonal projection jumps already obstruct this).

Neither the pinned Mathlib nor the audited current Mathlib master contains a projection-valued
measure or spectral-measure abstraction that removes this gap.  Current Mathlib does contain an
archived norm-topological Riemann--Stieltjes interface, but it is absent from the pinned revision,
is explicitly archived, and still does not model Sakai's strong-topology integrator.

## Revisions and evidence boundary

The distinctions below are intentional.

| Corpus | Audited revision | Date/evidence |
| --- | --- | --- |
| Sak-AI worktree | `463d37e86e1de217b65b2976f342db32393b6245` | assigned integration baseline |
| pinned Mathlib | `476ab284693e554a6b48c5f5210cb4fb5ae51252` | commit timestamp 2026-07-08 |
| current official Mathlib master | `2ca39e62989124794bd8405bb2e60805f63d37bc` | observed 2026-08-30 at commit timestamp 15:43:26 UTC |
| original LeanOA | `cb811c1006ae78a0ff1d175253200e1859843370` | read-only duplication comparison |

"Current" claims in this report refer only to the official Mathlib master revision above, not to
an unpinned future state.  GitHub pull-request status was observed on 2026-08-30.

The Sakai source was checked in the available scan, printed pages 26--27 (PDF pages 38--39).
Theorem 1.11.3 describes

`x = ∫ λ de(λ)`

as an abstract Radon--Stieltjes integral with respect to the `s(M, M_*)` topology. Its uniqueness
argument uses `(λ₀ 1 - x)⁺` and support.  Consequently, replacing this with a norm-valued vector
measure or merely displaying integral notation would not be a faithful translation.

At the audited baseline, the source theorem compares as follows:

| Sakai 1.11.3 clause | Sak-AI status |
| --- | --- |
| `e(λ)` is a projection-valued increasing family | represented by `spectralProjectionIio` and monotonicity |
| continuity from below | its weaker ultraweak consequence is kernel-proved; the source strong conclusion is not yet public |
| limits zero and one at the two endpoints | exact finite cutoff lemmas imply these limits in any topology; named production limits are ultraweak |
| `x = ∫ λ de(λ)` in the `s(M,M_*)` Radon--Stieltjes sense | lower/upper sums and norm convergence are proved for the canonical family; the exact integral-level statement/interface is unresolved |
| uniqueness of the resolution | not yet formalized as the source clause |

## Existing Sak-AI frontier

All declarations in this section were located in the named source and checked through a focused
build of `LeanOA.Ultraweak.SpectralApproximation`; the principal names were also elaborated with
`#check` against the pinned environment.

### Positive-part functional calculus

File: `LeanOA/CStarAlgebra/Spectral.lean`

- `CStarAlgebra.spectralPositivePart`
- `CStarAlgebra.spectralPositivePart_eq_posPart`
- `CStarAlgebra.spectralPositivePart_nonneg`
- `CStarAlgebra.continuous_spectralPositivePart`

This is the continuous-functional-calculus input used to recover half-line cuts by support.

### Half-line spectral projections

File: `LeanOA/Ultraweak/SpectralProjection.lean`

- `WStarAlgebra.spectralProjectionIio`
- `WStarAlgebra.spectralProjectionIio_eq_support_posPart`
- `WStarAlgebra.spectralProjectionIio_mono`
- `WStarAlgebra.spectralProjectionIio_band_bounds`
- `WStarAlgebra.spectralProjectionIio_eq_zero_of_le_neg_norm`
- `WStarAlgebra.spectralProjectionIio_eq_one_of_norm_lt`
- `WStarAlgebra.isLUB_range_spectralProjectionIio_of_tendsto`
- `WStarAlgebra.tendsto_spectralProjectionIio_atBot`
- `WStarAlgebra.tendsto_spectralProjectionIio_atTop`
- `WStarAlgebra.tendsto_spectralProjectionIio_of_monotone`

This gives the `Iio` convention, monotonicity, band estimates, endpoints, and continuity from below
in the ultraweak topology.  It is a spectral family, not yet a set-indexed PVM.

### Finite spectral sums and error estimates

File: `LeanOA/Ultraweak/SpectralSum.lean`

- `WStarAlgebra.lowerSpectralSum`
- `WStarAlgebra.upperSpectralSum`
- `WStarAlgebra.sum_spectralProjectionIio_sub`
- `WStarAlgebra.lowerSpectralSum_le_self`
- `WStarAlgebra.self_le_upperSpectralSum`
- `WStarAlgebra.norm_upperSpectralSum_sub_lowerSpectralSum_le`
- `WStarAlgebra.norm_self_sub_lowerSpectralSum_le`
- `WStarAlgebra.norm_upperSpectralSum_sub_self_le`

These are already the essential Darboux/Radon--Stieltjes estimates for the identity integrand.

### Convergence and a cofinal dyadic family

File: `LeanOA/Ultraweak/SpectralApproximation.lean`

- `WStarAlgebra.tendsto_lowerSpectralSum`
- `WStarAlgebra.tendsto_upperSpectralSum`
- `WStarAlgebra.dyadicSpectralMesh`
- `WStarAlgebra.dyadicSpectralCut`
- `WStarAlgebra.dyadicSpectralCut_refines`
- `WStarAlgebra.tendsto_dyadicSpectralMesh`
- `WStarAlgebra.tendsto_lowerSpectralSum_dyadic`
- `WStarAlgebra.tendsto_upperSpectralSum_dyadic`

The generic theorems use an arbitrary filter of meshes tending to zero; the dyadic declarations
give a concrete sequence and refinement law.  The convergence presently lands in the norm
topology, which is stronger than the source's topology.

### Existing topology bridge

File: `LeanOA/Ultraweak/Basic.lean`

- `continuous_toUltraweak`
- `Ultraweak.toUltraweakL`
- `Ultraweak.toUltraweakL_apply`

Thus a norm `Tendsto` theorem can be mapped directly to a `Tendsto` theorem with codomain
`σ(M, P)_𝕜`.  No new predual or topology is needed for the next theorem-level step.

## Pinned Mathlib audit

### Scalar measure and Bochner integration

Relevant sources:

- `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`: `MeasureTheory.integral`, ordinary
  scalar-measure Bochner integration, finite-sum and norm estimates;
- `Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`:
  `ContinuousLinearMap.integral_comp_comm`;
- `Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Integral.lean`:
  `cfc_integral'` and `cfc_integral`.

These APIs integrate scalar- or vector-valued functions against an already constructed scalar
measure.  They are useful after scalarization, and continuous linear maps can be passed through the
integral.  They neither construct a spectral measure nor integrate against an ultraweak
operator-valued integrator.  In particular, `cfc_integral` commutes CFC with an existing Bochner
integral; it is not a spectral theorem or a PVM constructor.

### Scalar Lebesgue--Stieltjes measures

File: `Mathlib/MeasureTheory/Measure/Stieltjes.lean`

- `Monotone.stieltjesFunction`
- `Monotone.stieltjesFunction_eq`
- `StieltjesFunction.measure`
- `StieltjesFunction.measure_Iio`

File: `Mathlib/Topology/Order/LeftRightLim.lean`

- `leftLim_rightLim`

For a normal positive functional `φ`, the scalar function
`r ↦ re (φ (spectralProjectionIio a r))` is a plausible route to a scalar Stieltjes measure.
Because the local family uses `Iio` and continuity from below, the exact left/right-limit
conventions must be proved; `Monotone.stieltjesFunction` and `leftLim_rightLim` supply the likely
alignment tools.  This route produces one scalar measure per `φ`, not a coherent M-valued PVM.
Recovering an element of `M` from all scalar integrals would additionally require normal-functional
separation, positivity/decomposition, and coherence results.

The pinned Riesz--Markov--Kakutani implementation in
`Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean`, notably
`RealRMK.rieszMeasure` and `RealRMK.integral_rieszMeasure`, offers another scalar representation
route after composing a positive functional with CFC.  It has the same reconstruction limitation.

### Vector measures: measure layer versus integral layer

File: `Mathlib/MeasureTheory/VectorMeasure/Basic.lean`

- `MeasureTheory.VectorMeasure`
- `MeasureTheory.VectorMeasure.m_iUnion`

The structure assumes only an additive commutative monoid and a topology on the codomain.  Its
countable-additivity field is a topological `HasSum`.  Therefore a future
`VectorMeasure ℝ (Ultraweak M P)` is type-correct in principle and could express ultraweak
countable additivity.

File: `Mathlib/MeasureTheory/VectorMeasure/Integral.lean`

- `MeasureTheory.VectorMeasure.Integrable`
- `MeasureTheory.VectorMeasure.integral`
- `MeasureTheory.VectorMeasure.integral_finsetSum`
- `MeasureTheory.VectorMeasure.norm_integral_le_lintegral_norm`

File: `Mathlib/MeasureTheory/VectorMeasure/SetIntegral.lean`

- `MeasureTheory.VectorMeasure.integral_indicator_const`

This is a different layer: the integral pairs real normed spaces by a continuous bilinear map and
defines integrability through `μ.variation`.  It is a norm/variation construction.  Giving `M` its
C-star norm would demand norm-additivity and bounded norm variation, which general spectral
families do not have.  Giving `M` the `Ultraweak` topology makes the measure structure plausible but
does not make this normed integral applicable to that topology.

### Bounded-variation vector Stieltjes measures

File: `Mathlib/MeasureTheory/VectorMeasure/BoundedVariation.lean`

- `BoundedVariationOn.vectorMeasure`
- `BoundedVariationOn.vectorMeasure_Ioc`
- `BoundedVariationOn.vectorMeasure_Iio`

This constructs a vector measure from a norm-bounded-variation function into a complete normed
additive group.  It is not a shortcut for a general spectral family: for infinitely many nonzero
orthogonal spectral bands, the norm of every projection jump is one, so the variation sums are
unbounded.  The mismatch is mathematical, not merely missing glue code.

### Tagged-partition integration

Relevant sources:

- `Mathlib/Analysis/BoxIntegral/Basic.lean`: `BoxIntegral.integralSum`,
  `BoxIntegral.HasIntegral`, `BoxIntegral.Integrable`, and `BoxIntegral.integral`;
- `Mathlib/Analysis/BoxIntegral/Partition/Filter.lean`:
  `BoxIntegral.IntegrationParams.Riemann`.

This is a norm-topological tagged-partition framework using a box-additive integrator.  It is useful
design evidence for a limit predicate, but the pinned tree has no Riemann--Stieltjes interval
wrapper, and `BoxIntegral.HasIntegral` still targets a normed output topology.

### PVM/spectral-measure result

Repository-wide source searches at the pinned revision found no `SpectralMeasure`,
`ProjectionValuedMeasure`, or equivalent general PVM abstraction.  Existing CFC projection results
do not turn arbitrary Borel half-lines into projections.

## Current Mathlib delta

At current official master `2ca39e6`, the basic conclusion is unchanged.

1. `Mathlib/MeasureTheory/VectorMeasure/Basic.lean` adds useful infrastructure including
   `VectorMeasure.of_biUnion` and `VectorMeasure.ext_of_generateFrom`.
2. `Mathlib/MeasureTheory/VectorMeasure/IntegrationByParts.lean` is new relative to the pinned
   revision, but it remains in the bounded-variation/vector-measure regime.
3. `Archive/RiemannStieltjes.lean` now defines
   `BoxIntegral.HasStieltjesIntegralOrdered`, `BoxIntegral.HasStieltjesIntegral`,
   `BoxIntegral.StieltjesIntegrable`, and `BoxIntegral.stieltjesIntegral`.  It uses
   `BoxIntegral.HasIntegral` and a normed continuous bilinear pairing.  The file itself recommends
   ordinary or vector-measure integration unless the specifically Riemann aspect is wanted.
   Because it is archived, absent from the pinned dependency, and norm-topological, it should be
   treated as a useful precedent rather than a foundation to copy locally.
4. Source-wide searches still find no general PVM or operator-valued spectral-measure abstraction.
5. Mathlib pull request [#42100](https://github.com/leanprover-community/mathlib4/pull/42100),
   open when audited, concerns clopen spectral projections.  Even if merged, clopen subsets do not
   cover the half-line cuts needed here because the intersection of a half-line with the spectrum
   need not be clopen.

No current-master delta makes an immediate dependency update the shortest route.

## Route comparison

| Route | What it honestly supplies | Main mismatch/blocker | Reversibility |
| --- | --- | --- | --- |
| Existing finite sums, with named ultraweak limit theorem | A useful topology-forgotten consequence of canonical norm convergence | Does not identify Sakai's strong abstract integral or supply a set-indexed PVM | High: theorem-only, no permanent object |
| Local topology-parametric `HasRadonStieltjesIntegral` predicate | Reusable proposition-level tagged-sum semantics in a chosen topology | Signature/partition conventions are a foundational choice; genericity must be justified | Medium-high if value-only; still requires review |
| Pinned `BoxIntegral.HasIntegral` | General tagged sums in a mature framework | Norm topology and box-additive-map interface, not ultraweak | Medium; an adapter risks encoding the wrong notion |
| Current archived `HasStieltjesIntegral` | Convenient norm Riemann--Stieltjes notation and API precedent | Not pinned, archived, norm-topological, no PVM | Medium-low as a dependency; high as read-only design evidence |
| Norm-valued `VectorMeasure ℝ M` plus its integral | Existing vector-measure integration lemmas | False general fit: spectral PVM is not norm-additive/bounded variation | Low; reject for the general theorem |
| Ultraweak-valued `VectorMeasure ℝ (Ultraweak M P)` | Correct topology for countable additivity at the measure layer | No matching integration; PVM laws and Borel extension still missing | Medium, but a large RED workstream |
| Scalarize by every normal positive functional | Genuine scalar Stieltjes measures and ordinary integration | Coherence/reconstruction of M-valued result; functional decomposition and separation | High but substantially longer |
| Direct set-indexed PVM | Natural endpoint for Borel functional calculus and uniqueness | No existing Mathlib core; must design additivity, orthogonality, normalization, scalarization, and integration | Low until consumers determine the API |

### Scalar versus vector Bochner integration

Ordinary Mathlib Bochner integration always integrates against a scalar nonnegative measure; its
output may be scalar or vector-valued.  This is distinct from the vector-measure integral, which
integrates against an `F`-valued measure through a bilinear pairing and variation.  Neither should
be described as an operator-valued spectral integral without first constructing the relevant
measure and proving the required topology/additivity facts.

### Operator-valued measure versus projection-valued measure

An operator-valued measure only records additivity.  A PVM also needs projection values,
normalization, orthogonality/multiplicativity on intersections, and the correct countable-sum
topology.  Sak-AI currently has a one-parameter half-line family; extending it to Borel sets and
proving these laws is genuinely new infrastructure.  Conflating these layers would hide rather
than solve the principal blocker.

## Duplication and upstream audit

No exact duplicates of the active Sak-AI declarations were found in the pinned Mathlib, the
audited current Mathlib master, or original LeanOA at the audited revisions.  In particular, the
search found no replacement for:

- the `spectralPositivePart` wrapper and its local support interface;
- the W-star half-line projection family `spectralProjectionIio`;
- the lower/upper spectral-sum band estimates;
- the generic mesh-to-zero and concrete dyadic convergence theorems.

Existing code already reuses Mathlib where the match is exact: for example,
`sum_spectralProjectionIio_sub` is built around the generic telescoping result
`Finset.sum_range_sub`.  No separate telescoping framework is warranted.

The dyadic mesh/cut arithmetic is abstract enough that a future repeated consumer might justify a
generic uniform-partition helper, but no exact existing Mathlib API or present second consumer was
found.  Refactoring it now would not shorten the route to 1.11.3.

Avoid locally duplicating current Mathlib's `BoxAdditiveMap.increment` or archived
`HasStieltjesIntegral` names.  If Sak-AI later needs a general tagged-limit predicate, first decide
whether that interface belongs upstream and whether its topology must be an explicit parameter.

## Recommendation: shortest honest reversible route

This report recommends the following direction without deciding a permanent integration API.

1. Integrate the already contracted tagged-spectral-sum theorem cluster using the current half-line
   projection and spectral-sum definitions.
2. Add a named theorem-level corollary whose conclusion is `Tendsto` in
   `σ(M, P)_𝕜`, obtained from the stronger norm estimate through
   `continuous_toUltraweak` or `Ultraweak.toUltraweakL`.
3. Document that theorem only as an ultraweak consequence of the canonical norm limit. Do **not**
   call it the formal semantics of Sakai's identity-integrand clause, introduce integral notation,
   claim a PVM, or mark the source theorem complete.
4. Preserve a later bridge theorem from this tagged-sum formulation to whichever PVM/integral
   object is eventually selected.

This advances the source theorem while making no irreversible choice about measurable-set
extension, integrator representation, or notation.

## Next bounded architecture transaction

After the tagged-sum cluster lands, open one bounded design transaction with this output only:

> Specify and test, in scratch modules, two candidate proposition-level signatures for the
> topology-parametric Radon--Stieltjes limit: (a) an adapter around a generic tagged-partition filter, and
> (b) a spectral-family-specific `HasSpectralIntegral` predicate.  Prove both candidates equivalent
> for the identity integrand using the landed norm estimates, list the minimum laws needed for a
> future bridge to a PVM, and make no public definition until review chooses between them.

Acceptance criteria for that transaction should include:

- the topology appears explicitly in the proposition or its codomain;
- the candidate supports arbitrary tags/mesh control rather than only one dyadic sequence;
- the identity-integrand theorem elaborates without any new measure object;
- no definition depends on norm bounded variation of the projection family;
- the design explains how source uniqueness via positive part/support will be stated separately;
- a deletion test shows the experiment can be removed without changing the landed spectral API.

Only after a real consumer needs characteristic functions, Borel sets, or general bounded Borel
functional calculus should Sak-AI choose among scalar reconstruction, an ultraweak vector-measure
extension, or a dedicated PVM.

## Blockers, classified

### Missing Mathlib infrastructure

- no general projection-valued measure/spectral-measure structure;
- no ultraweak-compatible integration API for topology-valued vector measures;
- no pinned Riemann--Stieltjes wrapper, and the current wrapper is normed and archived;
- no Borel extension theorem directly applicable to the local projection-valued half-line family.

### Missing Sak-AI infrastructure

- no set-indexed spectral measure/PVM;
- no public tagged spectral integral predicate;
- no scalarization-and-reconstruction bridge through the predual;
- source uniqueness for the resolution in 1.11.3 is not yet formalized.

### Mathematical formalization difficulty

- proving ultraweak countable additivity and PVM multiplication/orthogonality on all Borel sets;
- reconstructing an element of `M` coherently from scalar integrals;
- managing left/right continuity and atom conventions for `Iio` cuts;
- formalizing Sakai's uniqueness argument using positive parts and support.

### Statement-fidelity risk

- calling a norm/variation vector-measure integral Sakai's `s(M,M_*)` integral;
- proving only a preferred dyadic sequence while stating unrestricted Radon--Stieltjes semantics;
- treating an additive operator-valued measure as though PVM laws were automatic;
- marking 1.11.3 complete before the uniqueness clause is represented.

### Mere engineering work

- mapping the existing norm convergence through `toUltraweakL`;
- naming and documenting the ultraweak limit corollary;
- adding bridge lemmas after a reviewed interface is selected.

## Validation performed

- `lake build LeanOA.Ultraweak.SpectralApproximation` — success (3070 jobs).
- A scratch file importing the spectral frontier elaborated `#check` commands for the local and
  pinned declarations cited above — success.
- Every cited local source path and declaration was located by source search at the Sak-AI
  baseline.
- Pinned and current Mathlib revision hashes were obtained from their respective Git worktrees;
  current source was inspected in a temporary read-only sparse clone outside Sak-AI.
- Repository-wide searches for PVM/spectral-measure names were run in both pinned and current
  Mathlib sources and returned no general abstraction.
