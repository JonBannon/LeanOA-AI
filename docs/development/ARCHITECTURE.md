# Parallel-development architecture

This file operationalizes, but does not replace, the root `ARCHITECTURE.md` and the design contract.

## Layers and dependency direction

```text
Mathlib
  ↓
LeanOA/Mathlib staging (general, plausibly upstreamable gaps)
  ↓
functional analysis and C*-algebra infrastructure
  ↓
specified predual / ultraweak topology / W*-algebra bridges
  ↓
order, normality, projection, ideal, and support APIs
  ↓
Sakai theorem clusters (currently spectral resolution)
  ↓
Verso mathematical exposition and checked declaration links
```

The nested `docs/` package consumes the theorem package. It must never become a dependency of the
theorem package. Verso can reveal an awkward API, but foundational changes return to architecture
review rather than being designed independently in prose.

## Shared API policy

- GREEN APIs are safe downstream surfaces.
- YELLOW APIs may be consumed cautiously; do not expose their implementation details in new public
  interfaces.
- RED APIs have one architecture owner. Other streams state requirements rather than editing or
  replacing them.
- General facts go into `LeanOA/Mathlib/` only when their statement and namespace plausibly match
  Mathlib. Proof-local scaffolding stays private.
- Foundational representations, typeclass instances, and set-indexed spectral-resolution or
  integration objects require explicit review before adoption.

## Integration philosophy

The lead integrates in dependency order, checks design conformity before proof style, rejects
duplicate public foundations, and runs the full relevant build. Useful worker proofs may be retained
while their local wrappers are removed. Worktrees are disposable; accepted mathematics enters the
main branch only through reviewed commits.

The orchestration documents track work ownership and architecture only. The autonomous state and
ledger additionally record operational continuation, commit recovery points, and validation.
Mathematical status and dependency truth remain in Verso Blueprint blocks and `uses` references.

At the current Sakai 1.11.3 frontier, fixed-projection ultraweak decomposition is a reusable
downstream theorem layer. The source audit establishes that Sakai states the representation in his
strong `s(M,M_*)` topology, not the ultraweak topology, but leaves the integral's directed-division,
tag, refinement, and improper-endpoint semantics undefined. A scratch theorem checks the safe
topology-forgetting implication from strong convergence of the *same* finite-cut net to the
existing ultraweak conditional uniqueness chain. This does not certify that Sakai meant that net.
The resulting LEVEL C boundary does not authorize a public resolution, integral, or PVM
abstraction.

The exact canonical continuity theorem now lives in two downstream bridge modules:
`Ultraweak.StrongProjection` connects the existing projection lattice to the existing intrinsic
strong topology, and `Ultraweak.SpectralProjectionStrong` specializes that API to the lower
spectral family. This dependency direction is deliberate: neither foundational module imports the
other merely to host a bridge theorem. Sakai 1.11.1 is GREEN; the unrelated 1.11.3 integral
semantics remain RED.

Section 1.12 is complete through an independent CFC/support/ultraweak-compactness chain followed by
algebraic uniqueness. Element polar decomposition uses Mathlib `CFC.abs`, adds no duplicate
partial-isometry predicate, and lives in `Ultraweak.ElementPolarDecomposition`, distinct from the
existing functional `Ultraweak.PolarDecomposition` module.

Section 1.13 is a connective closeout rather than a new foundational normality layer. The
source-facing positive-directed bridge lives in `Ultraweak.NormalOrder`, downstream of the
canonical projection-normality/continuous-dual theorem. Arbitrary orthogonal projection sums live
in `Ultraweak.OrthogonalProjectionSum` as finite-subset/LUB/convergence theorems over the existing
projection subtype. `Ultraweak.ProjectionChain` supplies the minimal maximal-orthogonal
decomposition needed for the converse, while `Ultraweak.CompleteAdditivity` uses arbitrary-index
`HasSum` as its scalar semantics. Complete additivity remains theorem-level: no predicate or
parallel normality structure is public.

Section 1.14.2 adds functional support without changing the established element-support API.
`PositiveLinearMap.nullIdeal` is defined at the general unital $C^*$-algebra boundary, while
functional `PositiveLinearMap.support` is distinct from `WStarAlgebra.support` and requires an
explicit `IsNormalOnProjections` proof. Its chosen predual remains internal. Following Sakai's
dependency order, the null ideal is first proved closed in the intrinsic strong topology and then
ultraweakly closed through the existing convex strong-to-ultraweak closure theorem; the existing
closed-left-ideal classifier then supplies its unique projection generator. The faithfulness API
is theorem-level and reuses `IsStarProjection.Corner`: no `Faithful` predicate, normal-functional
bundle, null-support object, or competing corner structure is introduced.

Definition 1.14.1 adds `PositiveLinearMap.IsOrthogonal` at general nonunital $C^*$-algebra
generality, preserving Sakai's norm equality as the definition. Theorem 1.14.3 reuses the existing
self-adjoint-unitary positive factorization and private complementary corner cutdowns to expose one
`ExistsUnique` theorem for normal positive parts. Support-product zero is a downstream
characterization, and no choice-based parts, decomposition structure, normal-functional wrapper,
or second polar API is public.

Theorem 1.14.4 is implemented downstream in `Ultraweak.FunctionalPolarDecomposition`. The older
`Ultraweak.PolarDecomposition` is retained as the self-adjoint, self-adjoint-unitary, left-action
factorization needed by strong-topology work; it is not generalized or renamed into the source
theorem. The new module instead extends the same exposed-face method directly to the full unit
ball, then reuses functional support for its carrier and uniqueness arguments. Its convention is
Sakai's right action `g x = φ (x * v)`. `PositiveLinearMap.conjugate` is placed at nonunital
$C^*$-algebra generality, while preservation of normality and support transport remain in the
ultraweak layer. There is still no public partial-isometry predicate: the initial-support equation
is the established semantic certificate. The choice-based `Ultraweak.functionalAbs` is deliberate
because Sakai names the unique positive factor $|g|$ and the final-projection clause needs
$s(|g^*|)$; no choice-based polar element or decomposition structure is introduced.

Section 1.14 and Proposition 1.15.1 are complete. Proposition 1.15.2 remains the exact numbered
source frontier. Both its weak-family and strong-family clauses are now source-formalized
separately. Sakai's “bounded spheres” are zero-centered norm-closed balls, and the implemented
theorems give equality of the restricted topologies for arbitrary filters/nets. The quotient
predual is identified with the ambient ultraweak subspace topology at general
ultraweakly-closed-submodule and `RCLike` generality. The whole proposition is not yet
source-formalized because its two clauses have not yet been packaged in the exact printed order.

The first Section 1.15 transaction fixes the topology boundary without filling it by notation.
Mathlib's `ContinuousLinearMapWOT` is the concrete weak operator topology, and
`PointwiseConvergenceCLM` is its pointwise-convergence presentation of the strong operator
topology. The mirrored Mathlib bridge may therefore expose only the continuous identity
`PointwiseConvergenceCLM.toWOT` and the consequence that WOT-closed subsets of the underlying
continuous-linear-map space are pointwise/SOT closed. It introduces no new topology type.

The second Section 1.15 transaction constructs the finite vector-functional space at the generic
continuous-linear-map level. `ContinuousLinearMap.vectorFunctionalSpan` is the algebraic span of
`T ↦ ⟪η, T ξ⟫`; it separates operators and is stable under the intrinsic dual involution and fixed
left/right multiplication. `ContinuousLinearMapWOT.vectorFunctionalWeakEquiv` proves both identity
directions between its `WeakBilin` topology and Mathlib WOT. On the WOT carrier,
`ContinuousLinearMapWOT.vectorFunctionalPairing_isWeak` is the exact compatibility certificate,
and `vectorFunctionalSpanEquivDual` identifies the span with all WOT-continuous linear
functionals. No completion or predual is inferred from that algebraic/topological-dual result.

Sak-AI's `Ultraweak` topology `σ(M,P)`, intrinsic `Strong` topology `s(M,P)`, and Mackey topology
remain abstract specified-predual constructions. The intrinsic theorem
`Strong.isClosed_iff_image_toUltraweakEquiv` is a direct corollary of the established real-convex
closure-image theorem. It must not be read as an identification of `s(M,P)` with concrete SOT or
ultrastrong topology. Likewise, Sakai's separately defined $\sigma$-weak operator topology must not
be identified definitionally with `σ(B(H),B(H)_*)`; the source proves only the relevant closedness
equivalence here and postpones global topology identifications. The derived
`Strong.isClosed_ofStrong_preimage_iff_ofUltraweak_preimage` states this closure transport directly
for an arbitrary real-convex subset of the ambient algebra.

The direct source audit of Proposition 1.15.1, its finite WOT coefficient layer, norm-closed
coefficient predual, coefficient-series test topology, concrete ultrastrong carrier, and relative
Kaplansky theorem are complete. `Ultraweak.testWeakRestrictionL` reuses the existing generic
`WeakBilin.restrictRightL`, so the source series topology maps to the finite-core topology and then
to Mathlib WOT without a second topology implementation. The dedicated square-summable carrier
maps to pointwise/SOT, while positive diagonal coefficient series give the continuous identity
from intrinsic strong to that carrier. The final theorem keeps all five source predicates
distinct. Its difficult reverse edge identifies an ultraweakly closed subalgebra with its WOT
closure by applying relative Kaplansky density on the unit ball and then normalizing arbitrary
elements. `NonUnitalStarSubalgebra.operatorTopologyClosedness_tfae` therefore source-formalizes
Proposition 1.15.1 without asserting either later topology equality. IQ-010 is resolved, and the
public frontier advances to Proposition 1.15.2.

For Proposition 1.15.2, the induced predual is not a new foundational object. It is the existing
quotient `P / Ultraweak.preannihilator N` supplied by `Ultraweak.closedSubmodulePredual`.
`Ultraweak.closedSubmoduleEquivDual_apply_mk` and
`Ultraweak.closedSubmoduleUltraweakEquiv` now expose its pairing and canonical equivalence with
the ambient ultraweak subtype at general `RCLike` ultraweakly-closed-submodule generality. The nonunital
operator-algebra wrapper preserves this explicit quotient, and the source-specific weak-family
closed-ball comparison sits downstream in `Ultraweak.BoundedOperatorTopology`. Do not use the
choice-based `WStarAlgebra.predual N` as the primary construction, because it hides the restriction
map needed by the proof.

The strong-family layer follows the same carrier-safe design. `NonUnitalStarSubalgebra.InducedStrong`
is defined for any ultraweakly closed self-adjoint subalgebra of a dual $C^*$-algebra, independent
of a Hilbert-space representation. `BoundedOperatorTopology.SOTClosedBall` and
`BoundedOperatorTopology.USOTClosedBall` are generic over normed spaces and scalars. Only the
source comparison specializes to self-adjoint subalgebras of $B(H)$; it assumes ultraweak
closedness, which Proposition 1.15.1 identifies here with Sakai's WOT-closed hypothesis.
Filter-general positive-square criteria transport convergence through the already proved weak
closed-ball comparison and produce the three canonical strong-family homeomorphisms. These are
restricted-space results, not a global equality of intrinsic strong, ultrastrong, and SOT.

A cleaner direct proof that SOT and ultrastrong agree on every arbitrary operator-norm-bounded
subset—without any closed-algebra hypothesis—would improve the reusable concrete API. It is
deliberately deferred because the present source-faithful route is complete without it. The next
architectural transaction is instead the exact source-order two-clause package for Proposition
1.15.2.
