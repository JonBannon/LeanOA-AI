# Mathlib overlap and gap log

This is an API-reconnaissance log, not a commitment to upstream every helper.

## Already exists — reuse it

- Mathlib's native `TwoSidedIdeal` is the accepted Sak-AI representation.
- `IsStarProjection.le_iff_sub` supplies projection differences from order; do not re-prove the
  general result in Sak-AI.
- Mathlib's continuous functional calculus, self-adjoint subtype, and GNS construction are the
  foundations for the current C*-algebra and representation work.
- Standard filters, finite sums, and normed-space integration should be reused wherever their
  codomain assumptions fit; the spectral audit must determine where they stop fitting.

## Local helpers / plausible upstream candidates

- `IsStarProjection.mul_eq_self_of_nonneg_of_le_of_mul_eq_self` is a general hereditary-support
  lemma already isolated in the mirrored Mathlib hierarchy.
- The semiring-level annihilator lemmas may be upstreamable independently of the unresolved
  `TwoSidedIdeal` representation question.
- Generic weak-bilinear transport and compatibility lemmas should be compared to current Mathlib
  before further local expansion.
- Current Mathlib master contains `IsSelfAdjoint.norm_le_max_of_le_of_le`, but it is not an exact
  drop-in replacement for the pinned local declaration in `LeanOA/CFC.lean`: upstream assumes the
  middle element is self-adjoint, while the local signature derives that fact from a self-adjoint
  lower bound. On the next Mathlib update, remove the local duplicate and make the middle
  self-adjointness explicit at consumers such as tagged spectral sums.

## Major infrastructure question

- No accepted local set-indexed projection-valued-measure or operator-valued integration interface
  has been identified. Audit pinned and current Mathlib before introducing one. A scalar/vector
  Bochner integral is not automatically the right codomain for W*-algebra-valued spectral
  integration.

The completed audit in `reports/MATHLIB_SPECTRAL_AUDIT.md` distinguishes the implementation layers
precisely (its original identification of Sakai's topology has since been corrected):
`VectorMeasure` can express topology-parametric additivity, but its integral uses norm variation;
current `Archive/RiemannStieltjes.lean` is likewise norm-topological and is neither pinned nor a
general PVM. The existing theorem-level ultraweak tagged-sum limits remain useful consequences;
Sakai's printed source topology is the stronger `s(M,M_*)` topology.

## Spectral-integral interface experiment

D002 adds a narrower conclusion. At current-Mathlib commit `2ca39e6`,
`Archive/RiemannStieltjes.lean` is a useful design precedent: its named integral predicate is a
thin wrapper around `BoxIntegral.HasIntegral` only because `BoxIntegral` already owns tagged boxes,
Riemann/Henstock gauges, filter bases, eventual partition results, and a non-bottom theorem. It is
not a usable dependency for Sak-AI because it is absent from pinned Mathlib, norm-topological,
box-based, and its Riemann wrapper is mesh-only.

The endpoint geometry also needs an explicit adapter: Sak-AI's difference of two `Iio` spectral
projections represents `[r,s)`, whereas the box increment infrastructure is organized around its
own box convention. `Finpartition` provides refinement but not tags, ordered real endpoints, mesh,
or atom ownership. `SimpleFunc` does not remove the gap because spectral integration of its fibers
already requires a set-indexed projection assignment.

The scratch proofs further show that an abstract non-bottom canonical filter is not the missing
Mathlib object: after it is built, the proposed generic predicate is exactly `Tendsto`. The missing
content is the integrator's projection/additivity/continuity laws and honest treatment of atoms.
For the next continuous truncated-affine consumer, reuse generic `Tendsto` and the existing
norm-to-ultraweak map rather than adding a local integration hierarchy.

## First-wave general helper

- `IsStarProjection.sub_mul_sub_eq_zero_of_le` is a plausible Mathlib contribution: it is stated
  for nonunital $C^*$-algebras and says that differences from two ordered disjoint intervals in a
  chain of four projections are orthogonal. No equivalent was found in pinned or current Mathlib.

## Intrinsic strong topology and projections

Pinned Mathlib (`476ab284...`), the audited current Mathlib tree, and original LeanOA contain no
equivalent of Sak-AI's predual-indexed `Ultraweak.Strong` topology or the projection convergence
API added for Sakai 1.11.1. The general new results are plausible upstream candidates:

- eventual domination by a limiting projection upgrades ultraweak convergence to strong
  convergence;
- strong seminorm distance is monotone along nested projection intervals;
- the canonical net of a directed projection family converges strongly to its LUB.

They remain in a downstream Sak-AI bridge module because Mathlib currently has no matching
intrinsic topology in which to state them.

## Section 1.12 polar decomposition

Pinned Mathlib has the required canonical `CFC.abs`, sqrt/rpow/inverse/order APIs but no element
polar-decomposition theorem and no `IsPartialIsometry` predicate. Current Mathlib audited at
`be865aa50cc0364be66c3941a6dc0c845a2c2ceb` has the same gap. The audit found no duplicate polar
calculus in Sak-AI or the read-only original LeanOA either. Sak-AI now supplies the general
absolute-value annihilation lemmas `CFC.abs_mul_eq_zero_iff` and `CFC.mul_abs_eq_zero_iff`, plus
the consequences `IsStarProjection.mul_star_mul_self`, `mul_star_mul_self_assoc`, and
`mul_star_self`; these remain plausible upstream candidates. The proof-local regularizer needs no
new Mathlib abstraction: canonical sqrt/rpow/order results prove contractivity and norm
convergence, while Sak-AI's existing specified-predual closed-ball compactness supplies the later
ultraweak cluster point. The reviewed W-star bridge `WStarAlgebra.support_abs` / `support_abs_star`
then reuses Sak-AI's existing support universal properties; no equivalent appears in the audited
trees, and no new Mathlib object is needed. The W-star existence theorem itself belongs in Sak-AI
unless Mathlib first acquires a compatible W-star support/compactness layer. Sak-AI now supplies
that theorem as `WStarAlgebra.exists_element_polar_decomposition`, using a private regularizer and
ultraweak cluster-point proof. The general source consequence
`CFC.mul_star_eq_of_eq_mul_abs` has been placed in the mirrored layer at the abstract nonunital
real-CFC generality of Mathlib's absolute value; it is a small plausible upstream candidate. No
combined element-polar theorem or equivalent cutdown was found in pinned Mathlib, audited current
Mathlib, pre-WS-5 Sak-AI, or original LeanOA. Sak-AI now also supplies
`WStarAlgebra.element_polar_decomposition_unique` and the exact
`WStarAlgebra.existsUnique_element_polar_decomposition`; the former deliberately uses the existing
support zero-kernel and projection-fixing APIs rather than adding a more abstract one-use helper.

## Section 1.13 normality and complete additivity

Pinned and audited current Mathlib provide generic `ScottContinuous`/`ScottContinuousOn`, positive
linear maps, finite sums, and $C^*$-projection algebra, but no $W^*$-predual, ultraweak normality,
arbitrary $W^*$-projection sums, or unique-predual theorem. Sak-AI already has the hard theorem
`PositiveLinearMap.isNormalOnProjections_iff_mem_continuousDual`, directed projection LUB
convergence in both ultraweak and intrinsic strong topologies, and the canonical predual
equivalence. Original LeanOA contains only earlier specified-predual/ultraweak foundations.

Sak-AI now supplies the connective source-normality and orthogonal-sum layers. The former reuses
Mathlib `ScottContinuousOn`; the latter combines the standard finite-sum API with Sak-AI's
projection lattice and convergence API. Mathlib's `OrthogonalIdempotents` finite-sum theorem is
currently unital, whereas `IsStarProjection.finset_sum` now needs only a
`NonUnitalNonAssocSemiring` and `StarAddMonoid`. That theorem is a plausible small upstream
generality improvement, though it remains in the downstream module for its current single
consumer.

Sak-AI now closes the previously recorded complete-additivity gap. Mathlib `HasSum` supplies the
correct arbitrary-index finite-subset scalar semantics, while Sak-AI supplies the missing maximal
pairwise-orthogonal decomposition of a projection chain, with finite sums dominated by chain
members and supremum equal to the chain LUB. The chain-restricted Scott-continuity bridge then
recovers the canonical normality predicate. No audited Mathlib or original LeanOA declaration
supplied these results.

Small upstream candidates exposed by the proof are the nonnegative-complex
`HasSum`/finite-subsum-`IsLUB` equivalence, finite orthogonal projection-sum domination by a common
upper projection, and commutation with a fixed element at a directed projection LUB. The full
maximal decomposition and normality characterization remain naturally downstream until their
operator-algebra assumptions and naming receive broader review. Sak-AI deliberately publishes no
complete-additivity predicate, no bare `tsum` equality, and no competing normality structure.

## Section 1.14.2 functional support

Pinned Mathlib (`476ab284...`), audited current Mathlib (`567908cf...`), and original LeanOA
(`cb811c...`) contain no functional-support or GNS-null-left-ideal API for positive functionals.
Mathlib does supply the canonical `PositiveLinearMap`, GNS, `Ideal`, projection, and convexity
objects; current Sak-AI supplies projection normality, the intrinsic strong topology and its
convex-closure bridge, the ultraweakly closed left-ideal classifier, element support, and corners.
The accepted implementation composes those objects rather than adding a parallel foundation.

The reusable general additions are:

- the paired Cauchy--Schwarz consequences
  `PositiveLinearMap.apply_star_mul_eq_zero_of_apply_star_mul_self_eq_zero_left` and
  `PositiveLinearMap.apply_star_mul_eq_zero_of_apply_star_mul_self_eq_zero_right`, stated under the
  same natural assumptions as the existing coefficient estimate;
- `Ideal.mem_span_singleton_one_sub_iff_mul_eq_zero`, stated for an idempotent in a ring.

`PositiveLinearMap.nullIdeal` itself is kept at the natural general unital $C^*$-algebra boundary,
with no normality or $W^*$-algebra assumption. The support construction remains downstream because
Mathlib has no compatible $W^*$-predual, intrinsic strong topology, or closed-left-ideal classifier.
Its explicit normality proof, hidden chosen predual, and separation from element support are
intentional portability decisions. No general `Faithful` predicate or corner structure is needed;
the theorem-level consequences reuse `IsStarProjection.Corner`. The requested 1.14.3 overlap audit
is now complete below; it preceded every new functional-decomposition declaration.

## Section 1.14.1 and 1.14.3 norm orthogonality and Jordan decomposition

The completed audit in `reports/SAKAI_1_14_1_1_14_3_SOURCE.md` found no matching functional Jordan
decomposition or positive-functional norm-orthogonality API in pinned Mathlib, audited current
Mathlib, original LeanOA, or baseline Sak-AI. Mathlib's `MeasureTheory.JordanDecomposition` concerns
signed measures, and existing `IsOrthogonal`, `Disjoint`, positive/negative-part, and CFC APIs refer
to different principal objects. They cannot faithfully replace Sakai's Definition 1.14.1.

`PositiveLinearMap.IsOrthogonal` is consequently new, but is stated at its natural general
nonunital $C^*$-algebra boundary. The $W^*$-specific decomposition remains downstream in
`Ultraweak.existsUnique_orthogonal_decomposition_of_isSelfAdjoint`. Its implementation reuses the
existing `Ultraweak.exists_positive_comp_mulLeft_of_isSelfAdjoint`, functional support, corner
cutdowns, and normality bridges rather than adding ordered-dual or normal-functional foundations.

Mathlib does provide `IsStarProjection.two_mul_sub_one_mem_unitary`, the forward passage from a
projection to a self-adjoint unitary. No reverse splitting theorem or matching functional
centrality lemma was found. Both reverse steps remain private because the present wave has only one
consumer; they become upstream candidates only if a second independent use appears. The public
reusable additions are instead `PositiveLinearMap.support_le_iff_apply_eq_apply_one` and the
support/norm-orthogonality implications. The exact arbitrary-normal-functional overlap audit has
now been completed below; it does not reinterpret the self-adjoint factorization used for Theorem
1.14.3.

## Section 1.14.4 general normal-functional polar decomposition

Pinned Mathlib (`476ab284...`), audited current Mathlib (`567908cf...`), original LeanOA
(`cb811c...`), and baseline Sak-AI contain no arbitrary normal-functional polar decomposition with
Sakai's exact right-action, norm, initial-support, uniqueness, and final-support clauses. Existing
Sak-AI `Ultraweak.PolarDecomposition` is materially narrower: its input is self-adjoint, its
implementing element is a self-adjoint unitary, and its factorization uses left multiplication.
It remains a valid internal engine but cannot be relabeled as Theorem 1.14.4.

The completed implementation adds no competing foundational object. It extends the exposed-face
argument directly to the full unit ball in `Ultraweak.FunctionalPolarDecomposition`, uses the
existing `PositiveLinearMap.cutoff` for the source formula `g x = φ (x * v)`, and reuses functional
support for the carrier and uniqueness proofs. `IsStarProjection (star v * v)` follows from the
initial-support equality, so the absence of a Mathlib `IsPartialIsometry` predicate is not a
blocker and no local predicate was introduced.

The reusable C-star addition is `PositiveLinearMap.conjugate`, defined at nonunital generality as
`x ↦ φ (star a * x * a)`. Preservation of projection normality belongs downstream because it
depends on Sak-AI's specified-predual bridge. The support-transport theorem
`PositiveLinearMap.support_conjugate_eq_mul_star` is $W^*$-specific. The normal pullback theorem
`PositiveContinuousLinearMap.comp_toUltraweakPosCLM_isNormalOnProjections` consolidates a repeated
Sak-AI proof and is now reused by the earlier Jordan module.

`Ultraweak.functionalAbs` is intentionally local rather than an attempted Mathlib replacement: it
is the unique positive factor of a specified-predual normal functional and is needed to state
Sakai's final-projection identity as support of the absolute value of the adjoint. No chosen polar
element, normal-functional bundle, or general ordered-dual absolute value is added. The next
overlap audit is Section 1.15's topology and API boundary, beginning with Proposition 1.15.1.

## Section 1.15.1 concrete operator-topology audit

Pinned Mathlib commit `476ab284693e554a6b48c5f5210cb4fb5ae51252` already provides the two
concrete topology-bearing types that should be reused:

- `ContinuousLinearMapWOT`, with coefficientwise convergence and the Hilbert-space inner-product
  API, is the weak operator topology;
- `PointwiseConvergenceCLM` is pointwise convergence of continuous linear maps and is the strong
  operator topology in the concrete Hilbert-space specialization.

The mirrored Sak-AI Mathlib module adds only the missing general comparison:
`PointwiseConvergenceCLM.toWOT` and
`PointwiseConvergenceCLM.isClosed_pointwise_of_isClosed_wot`. These declarations state the
continuous SOT-to-WOT identity and its WOT-closed-to-SOT-closed consequence without defining a new
topology or adding Hilbert-space assumptions.

Classification: the two topology-bearing types and compatible-dual closure engine are
`PINNED VERSION ALREADY HAS IT`; the continuous pointwise/SOT-to-WOT map was `LOCAL BRIDGE
NEEDED`; the concrete predual, one-sided coefficient-series, and relative-closure layers were
`LOCAL BRIDGE NEEDED` and are now implemented in Sak-AI. Current
naming-only changes are `NOT RELEVANT`. No currently available upstream theorem
is `USABLE NOW` beyond the pinned APIs. An eventual upstream replacement for the local bridge is a
`FUTURE MATHLIB MIGRATION CANDIDATE`, but none was found in the audited current tree.

Neither pinned nor the official Mathlib `master` tree inspected on 2026-09-01 supplies a concrete
predual of $B(H)$, a bridge from the concrete von Neumann algebra/double-commutant presentation to
the abstract $W^*$-predual
presentation, a concrete $\sigma$-weak operator topology, or the square-summable-vector
ultrastrong topology. Current Mathlib's von Neumann algebra file continues to list the
abstract/concrete equivalence and double-commutant theorem as future work. Original LeanOA commit
`cb811c1006ae78a0ff1d175253200e1859843370` adds no concrete topology or predual bridge.

Sak-AI already owns the abstract specified-predual topologies `Ultraweak` (`σ(M,P)`),
`Ultraweak.Strong` (`s(M,P)`), and its Mackey/test-space machinery. The new intrinsic
`Strong.isClosed_iff_image_toUltraweakEquiv` merely packages the existing compatible-dual
real-convex closure theorem. It does not identify intrinsic strong with concrete SOT or
ultrastrong topology. Likewise, concrete $\sigma$-WOT must not be silently identified with
`σ(B(H),B(H)_*)`.

The main remaining infrastructure is therefore semantic rather than notational. Sak-AI now takes
the finite coefficient span to its norm closure, certifies that closure as the concrete $B(H)$
predual, and proves the source-safe continuous identity from the full predual topology to the weak
topology generated by countable square-summable coefficient series. The reverse comparison is a
later Sakai representation theorem and remains intentionally unclaimed. It remains to prove the
ultrastrong comparison. The Kaplansky engine now accepts an explicit test-weak-closure target, and
the finite coefficient core specializes it to Mathlib's WOT closure without a new topology or
predual. Until the concrete ultrastrong bridge and source theorem assembly exist, Sakai
Proposition 1.15.1 remains **not source-formalized**.

### Finite vector-functional layer and completion reconnaissance

Pinned Mathlib has no bundled functional `T ↦ ⟪η,Tξ⟫`, so Sak-AI now composes the existing
`ContinuousLinearMap.apply` and `innerSL` APIs. The resulting algebraic span is proved to induce
Mathlib WOT exactly, and Sak-AI's generic weak-representation theorem identifies it with the full
WOT-continuous dual. Classification: `LOCAL BRIDGE NEEDED`, now implemented without a new topology
type. The intrinsic dual involution reuses Mathlib's `WithConv` star rather than defining another
dual-star operation.

Neither pinned Mathlib nor the official `master` tree inspected on 2026-09-01 supplies a ready
infinite-dimensional `TraceClass`, `HilbertSchmidt`, Schatten, or nuclear-operator ideal suitable
as `B(H)_*`. Pinned Mathlib does supply rank-one maps, Hilbert-basis/ℓ² infrastructure, algebraic
tensor products, and projective seminorm machinery; current `SingularValues` remains
finite-dimensional and explicitly leaves infinite-dimensional approximation numbers as future
work. These are ingredients, not a concrete predual.

The completion-first construction is now implemented: `P_H` is the norm closure of the finite
coefficient span inside the norm dual, and canonical evaluation gives
`B(H) ≃ₗᵢ StrongDual ℂ P_H`. Sakai identifies this predual with trace-class operators only later in
Theorem 1.15.3, so trace class remains correctly absent from Proposition 1.15.1 infrastructure.
Exact reconnaissance and official-current links are recorded in
`reports/BH_PREDUAL_SIGMA_WOT_RECON.md`; coefficient-series membership and the permitted
one-sided topology comparison, together with ambient-relative WOT-closure density, are now
implemented. The next gap is the concrete square-summable-vector ultrastrong comparison.

## Radon--Stieltjes refinement audit

The exact audit in `reports/RIEMANN_STIELTJES_EXTERNAL_AUDIT.md` confirms that pinned Mathlib already
contains the generic machinery Sak-AI should reuse: `Finset` inclusion/union, `Set.Ici`,
`map_val_Ici_atTop`, `atTop_Ici_eq`, `tendsto_comp_val_Ici_atTop`, metric finite approximations of
totally bounded intervals, and filter-basis nontriviality lemmas. These suffice for prescribed cuts
and for a checked nontrivial refinement-plus-mesh candidate filter.

No audited library supplies the missing semantic object. PNT+'s implemented filter is scalar,
fixed-interval, and mesh-only; teorth's scalar Darboux development has placeholders; current
Mathlib's archived Riemann--Stieltjes API and the ICERM work are fixed-box and norm-topological.
Accordingly the remaining gap is not another generic cofinality theorem. Sakai's source clause is
strong-topological, while its operator-valued division/refinement and improper-limit semantics are
LEVEL C ambiguous. No source-certified representation predicate is currently justified.

## CFC audit for truncated-affine recovery

At pinned Mathlib commit `476ab284`, the public unital CFC is already algebra-and-predicate based:
`ContinuousFunctionalCalculus R A p` supplies the bundled `cfcHom`, while ordinary clients use
`cfc`. Composition, uniqueness, restriction/range, order, and the positive-part identity are all
part of that architecture. Sak-AI's `CStarAlgebra.spectralPositivePart` is therefore intentionally
only a source-facing name for `cfc (fun x : ℝ => (r - x)⁺) a`; its equality with
`(algebraMap ℝ A r - a)⁺` reuses Mathlib's `CFC.posPart_def`, composition, subtraction, constants,
and the identity function.

The new truncated-affine theorem needs no local continuous calculus. Its canonical band estimates
identify finite spectral sums directly with the existing `spectralPositivePart`, and its
ultraweak statement merely transports the already-proved norm limit through `toUltraweak`.
The topology defining CFC and the topology of spectral-sum convergence remain separate.

Current Mathlib commit `e62ea4d7200989bad96e0cc05b349c1a5c9800c8` contains an upstream
`ContinuousFunctionalCalculus/Transfer.lean` substantially matching Sak-AI's pinned staging layer,
as well as interval-norm helpers relevant to the existing local order API. These are future
dependency-update migration candidates, not usable at the pinned revision. During that update,
check the current nonunital transfer namespace spelling before deleting local staging. Neither the
pinned nor audited current tree supplies a general projection-valued measure or an operator-valued
spectral integral.

## External work already monitored

Root `REVIEW_QUEUE.md` records the authoritative status of Mathlib PRs #42093, #42095, and #42100
and the completed overlap audits for Sections 1.10 and 1.11.1. Do not duplicate or silently update
those conclusions here; append only new evidence with commit/revision identifiers.
