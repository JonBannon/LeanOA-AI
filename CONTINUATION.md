# Sak-AI mathematical continuation

Last updated: 2026-09-01

## Verified repository state

- Branch: `master`.
- Parallel orchestration began from `92db74d`; worker worktrees were cut from coordination commit
  `463d37e`.
- The first parallel spectral wave adds theorem-level band calculus and arbitrary tagged spectral
  sums without changing the lower spectral projection or choosing a spectral-measure object.
- The truncated-affine recovery transaction adds a theorem-only CFC bridge and leaves the
  arbitrary-resolution, PVM, and operator-valued integral boundaries explicitly RED.
- The fixed-projection transaction adds the general ultraweak positive/negative decomposition and
  support helper API. At that stage the full competing-resolution chain was kernel-checked
  conditionally and the source representation-to-refinement bridge remained RED.
- The Radon--Stieltjes refinement transaction kernel-checks prescribed-cut cofinality, a nontrivial
  refinement-plus-mesh filter with asymptotic endpoints, and complete pointwise/family uniqueness
  under an explicit left-endpoint moment limit. Source equivalence with Sakai's undefined abstract
  integral remains RED, so no candidate declaration is public or documented as complete.
- The source-certification transaction corrects a prior reading: Sakai prints the strong
  `s(M,M_*)` topology in Lemma 1.11.1 and Theorem 1.11.3, not the ultraweak `σ(M,M_*)` topology.
  A full internal and period-literature audit classifies the undefined integral semantics LEVEL C.
  The same-net strong-to-ultraweak implication is kernel-checked in scratch; it does not identify
  Sakai's division/filter semantics.
- The subsequent 1.11.1 transaction proves the exact source statement: arbitrary real sequences
  converging to a cut from below give convergence of the lower spectral projections in the
  intrinsic strong topology, with no monotonicity hypothesis. General projection-LUB strong
  convergence and filter-level left continuity are now public.
- Section 1.12 is source-formalized from accepted-input baseline
  `9476b69357b8d2f6c9884b363f5378098d3ac039`. The exact Sakai regularizer is private production
  scaffolding; filter-based ultraweak compactness and the source cutdown `u = q * b * p` prove the
  factorization and both support equations in
  `WStarAlgebra.exists_element_polar_decomposition`. No duplicate polar calculus,
  partial-isometry predicate, compactness layer, or exposed predual was introduced. Algebraic
  uniqueness uses only the factorization and initial-support equations, and
  `WStarAlgebra.existsUnique_element_polar_decomposition` packages exact Theorem 1.12.1.
- Section 1.13 is complete. The first wave connected the literal bounded directed-positive
  definition to projection normality, full Scott continuity, and specified-predual membership and
  packaged arbitrary orthogonal projection `Finset` sums with their LUB and ultraweak/strong
  convergence. The second wave supplied the maximal orthogonal decomposition of projection chains,
  chain-restricted Scott continuity as a sufficient normality criterion, and the theorem-level
  arbitrary-family `HasSum` characterization. No second normality or complete-additivity predicate
  was added.
- Sakai 1.14.2 is source-formalized. The general positive-functional null left ideal is public at
  the unital $C^*$-algebra boundary. For a normal positive functional, its strong closedness and
  the convex strong-to-ultraweak closure bridge feed the existing closed-left-ideal classifier.
  `PositiveLinearMap.support` hides the canonical predual and exposes the exact right-annihilator,
  greatest-zero-projection, cutdown, full-support, and derived faithful-corner interfaces. No
  second element-support object, normal-functional bundle, faithfulness predicate, or corner was
  added.
- Sakai Definition 1.14.1 and Theorem 1.14.3 are source-formalized. Norm orthogonality is the
  general nonunital $C^*$-level relation `PositiveLinearMap.IsOrthogonal`; for normal positive
  functionals it is equivalent to zero product of their intrinsic supports. The existing
  self-adjoint-unitary positive factorization supplies the unique normal positive decomposition,
  exact difference, and norm sum. No choice-based parts, decomposition structure, normal-
  functional wrapper, or competing polar API was added.
- Sakai Theorem 1.14.4 is source-formalized, completing Section 1.14. The exact source convention
  is `R_v φ (x) = φ (x * v)`. The public unique pair consists of a normal positive functional and
  a multiplier with equal norm, initial projection `star v * v = support φ`, and final projection
  `v * star v = support |g⋆|`. The canonical positive factor is `Ultraweak.functionalAbs`.
  `PositiveLinearMap.conjugate` is C-star-general and support transport reuses the intrinsic
  functional-support API. No new partial-isometry predicate or second support hierarchy was added.
- The theorem package had no uncommitted changes at the start of the orchestration work.
- Jireh Loreaux's LeanOA and Mathlib are read-only references. The original LeanOA checkout has
  not been modified.

## Mathematical frontier

Sakai 1.10.3--1.10.7 and Lemmas 1.11.1--1.11.2 are complete, and the spectral-resolution
development now includes norm
convergence of arbitrary tagged finite spectral sums in Sakai 1.11.3: lower spectral projections are
constructed, proved strongly continuous from below under Sakai's exact nonmonotone hypotheses (and
ultraweakly continuous for directed monotone nets), satisfy Sakai's increment and
endpoint formulas, and yield lower and upper finite sums converging in norm along arbitrary
mesh-zero filtered families and an explicit nested sequence of dyadic divisions. Spectral-band
differences now have a reusable projection/commutation/additivity/orthogonality API. Arbitrary tags
inside the bands give sums between the lower and upper sums, with the same mesh estimate, norm
limit, and an explicit limit in every specified ultraweak topology.

Truncated-affine weights are now covered as well. For every cutoff $r$, including one lying
strictly inside a partition band, the corresponding weighted tagged sum is within the mesh of
`CStarAlgebra.spectralPositivePart a r`, hence converges in norm and in every specified ultraweak
topology to the existing Mathlib-CFC value $\operatorname{cfc}(x\mapsto(r-x)^+)(a)$. No new
continuous calculus, spectral integral, lower-family structure, or PVM was introduced.

The fixed-projection analytic step in Sakai's uniqueness paragraph is now public at the weakest
natural level. An eventual identity `p * (u_i-v_i)=u_i` separates the specified-ultraweak limits;
when `p` is a star projection and the two pieces are eventually nonnegative, their limits are the
Mathlib positive and negative parts. The source-accurate finite cutoff algebra, both support
inequalities, continuity-from-below recovery, and uniqueness are kernel-checked in scratch. A
concrete nontrivial filter now combines finite-cut inclusion refinement with shrinking maximum
adjacent mesh; its extrema escape and inserting any fixed cuts is eventually the identity. Under
convergence of the corresponding left-endpoint identity moments, the full pointwise and family
uniqueness assembly checks. This is not yet the source theorem because Sakai states an abstract
strong-topology Radon--Stieltjes integral but does not define its Moore--Smith, tag, refinement, or
improper-endpoint semantics. No source-reviewed predicate has therefore been accepted.

The independent Section 1.12 chain is now public. The general annihilator,
partial-isometry, and absolute-value support APIs feed a private copy of Sakai's contractive
regularizer. `Ultraweak.isCompact_closedBall` and a mapped-filter cluster point give a contraction
`b` with `b * CFC.abs a = a`; the exact cutdown `u = q * b * p` then proves
`a = u * CFC.abs a`, `star u * u = support |a|`, and
`u * star u = support |star a|`. The public theorem has the ordinary `WStarAlgebra` context and no
chosen-predual parameter. The source consequence for `a * star a` is separately available as
`CFC.mul_star_eq_of_eq_mul_abs` at abstract nonunital real-CFC generality. The support zero-kernel
theorem turns `(u-v) * CFC.abs a = 0` into `(u-v) * support |a| = 0`; the initial-support equations
then give `u = v`. The exact `ExistsUnique` package includes both source support equations.

Section 1.13 is source-formalized in full. The canonical predicate remains
`PositiveLinearMap.IsNormalOnProjections`; its exact source characterization uses
`ScottContinuousOn` on norm-bounded nonnegative sets. For an arbitrary orthogonal family, the
`Finset` partial sums converge ultraweakly and strongly to the existing projection `iSup`, and
normality is equivalent to `HasSum (fun i ↦ φ (p i)) (φ (⨆ i, p i))`. The forward theorem supports
an index type in an independent universe. The converse uses a same-algebra-universe family because
the Zorn decomposition is subtype-indexed; after normality is recovered, the forward theorem gives
the fully universe-polymorphic result.

Sakai Section 1.14 is now source-formalized. For a normal
positive functional `φ`, the null left ideal is `M (1 - s(φ))`, so
`φ (star x * x) = 0 ↔ x * s(φ) = 0`; the complement is the greatest projection killed by `φ`.
Sakai's orthogonality relation is exactly `‖φ - ψ‖ = ‖φ‖ + ‖ψ‖`, and for normal positive
functionals it is equivalent to `s(φ) * s(ψ) = 0`. Every self-adjoint normal functional has a
unique orthogonal normal positive/negative decomposition with the exact additive norm identity.
Every normal functional `g` also has a unique Sakai polar pair `(v, |g|)` with
`g(x) = |g|(x * v)`, equal norm, `star v * v = s(|g|)`, and
`v * star v = s(|g⋆|)`. The next bounded source target is the concrete operator-topology setup
and Proposition 1.15.1; it requires an API audit of WOT, SOT, ultrastrong, sigma-weak, and predual
topologies before implementation.

The implemented public design is:

1. Define one-sided annihilators over semirings using infima of `LinearMap.ker`; encode right
   ideals as `Ideal (MulOpposite R)`.
2. Package annihilators of one-sided ideals as native `TwoSidedIdeal R` under Mathlib's current
   ring assumption. Do not introduce a competing structure.
3. Prove ultraweak closedness as intersections of kernels of existing continuous fixed-
   multiplication maps.
4. Add a reusable ultraweak linear homeomorphism between an algebra and its multiplicative
   opposite, induced by predual transport.
5. Define public left and right supports by infima in the existing complete lattice of star
   projections, leaving predual choices inside proofs.
6. Promote the private internal-unit-is-projection fact from `LeanOA/Ultraweak/Ideal.lean` to a
   reusable algebraic lemma and refactor the existing proof to use it.
7. Build a nonunital analogue of the existing `StarSubalgebra.ultraweakClosure` API by reusing
   Mathlib's `NonUnitalStarSubalgebra.topologicalClosure`.
8. State Sakai 1.10.5 for native `TwoSidedIdeal M`; restrict the projection/closed-left-ideal
   order isomorphism to central projections and closed two-sided ideals.
9. Define central support by the complete lattice of central projections and expose leastness,
   monotonicity, idempotence, and fixed-point lemmas.
10. Put the projection identity `p * q = 0 ↔ p ≤ 1 - q` in the general unital C-star projection
    API, then prove Sakai 1.10.7 and the reusable iff strengthening.
11. Define the scalar cutoff `(r • 1 - a)⁺` in a C-star-only module, then define its support as
    `WStarAlgebra.spectralProjectionIio`; first prove the ultraweak monotone-net theorem, then the
    exact strong nonmonotone statement of Sakai 1.11.1 through the downstream topology bridge.
12. Reuse support and projection-order APIs to prove the spectral-band bounds and Sakai 1.11.2,
    strengthening the cut hypothesis from `<` to `≤`.
13. Prove the endpoint formulas with sharp inequalities and derive their ultraweak limits from
    eventual constancy. Keep the reusable positive-scalar lower-bound criterion in the support API.
14. Define finite spectral sums directly over `Finset.range`, reuse Mathlib's telescoping identity,
    and derive the bracketing, order-gap, and norm-error estimates from the existing band theorem.
15. Derive convergence for arbitrary filtered families directly from the finite norm-error API;
    give a concrete dyadic family whose elementary grid lemmas only require a seminormed additive
    star group, and prove its divisions refine on the nose.
16. Extract ordered-disjoint projection-difference orthogonality at nonunital $C^*$-algebra
    generality, then expose the spectral-band specialization without bundling a spectral family.
17. Define arbitrary tagged spectral sums, bridge their endpoint tags back to the existing lower
    and upper sums, prove sandwich/error/convergence theorems, and pass the norm limit through the
    canonical map to every specified ultraweak topology.
18. Prove a reusable partial-interval estimate and sharp truncated-affine mesh estimate without
    requiring the cutoff to be a partition point; target the existing CFC positive part and derive
    filter-general norm and specified-ultraweak convergence.
19. Isolate the fixed-projection limit argument at ordered $C^*$-algebra generality, derive the two
    individual limits from one extraction identity, and identify them as positive/negative parts
    using ultraweak order closure. Add the symmetric projection-support simp API and the reusable
    positive-scalar lower-bound criterion. Keep competing-resolution recovery conditional until
    the source representation/refinement bridge is formalized.
20. Reuse `Finset` inclusion and Mathlib's `Ici` filter theorems for prescribed cuts; combine
    refinement with a checked shrinking-mesh coordinate without exact finite endpoints; prove
    simultaneous feasibility by finite metric nets; and assemble the abstract moment bridge,
    finite split, support recovery, pointwise identification, and family uniqueness under the
    explicit candidate semantics. Keep the result scratch-only pending source-equivalence review.
21. Connect the projection lattice to the intrinsic strong topology downstream: eventual
    domination plus ultraweak convergence upgrades projection nets to strong convergence, directed
    LUBs converge strongly, and a nested-projection seminorm squeeze proves exact filter-level left
    continuity and Sakai's nonmonotone sequential Lemma 1.11.1.
22. Keep Mathlib `CFC.abs` canonical and add only the general nonunital $C^*$-algebra bridges:
    exact one-sided annihilator equivalences and the fixing/final-projection consequences of
    `IsStarProjection (star u * u)`. Keep Sakai's regularizer proof-local until the element-polar
    existence theorem gives it a production consumer.
23. Put the CFC-to-W-star bridge in a narrow downstream module: rewrite support of `CFC.abs a` to
    `rightSupport a` and support of `CFC.abs (star a)` to `leftSupport a`, without importing CFC
    back into foundational `Ultraweak.Support` or adding a normality assumption.
24. Keep Sakai's regularizer and cluster-point construction private; expose only the element-polar
    existence theorem and both canonical support equations. Put the independent modulus-square
    consequence at the abstract CFC boundary rather than retaining unnecessary $C^*$ or $W^*$
    assumptions.
25. Prove polar-factor uniqueness directly from the support zero-kernel theorem and the two
    initial-support fixing identities. Preserve the existence-only theorem, package exact
    `ExistsUnique`, and do not add a `polarPart` or partial-isometry predicate without a consumer.
26. Keep `IsNormalOnProjections` canonical and characterize it through full Scott continuity and
    Sakai's bounded nonnegative `ScottContinuousOn` condition; prove the printed boundedness clause
    redundant once an `IsLUB` is supplied, and keep intrinsic statements free of a chosen predual.
27. Represent arbitrary orthogonal projection sums by `Finset` partial sums and the existing
    projection `iSup`; expose algebraic, LUB, ultraweak, and strong theorem layers without a new
    family structure, notation, or `tsum` interpretation.
28. Use arbitrary-index `HasSum` for scalar complete additivity. Keep the API theorem-level: the
    projection-chain decomposition route now kernel-checks both implications, so no predicate is
    needed.
29. Define `PositiveLinearMap.nullIdeal` before normality at the general unital $C^*$-algebra
    boundary. For a normal positive functional, follow Sakai's strong-to-ultraweak closure route,
    reuse the existing closed-left-ideal classifier, and define one intrinsic
    `PositiveLinearMap.support` with its chosen predual hidden. Keep functional and element support
    separate, orient nullity as right annihilation, and express faithfulness through theorem-level
    statements on the existing corner API.

## Implementation order

The completed implementation layers are:

1. General algebraic layer (completed on 2026-08-27):
   - `IsStarProjection.mul_eq_zero_iff_le_one_sub`;
   - `Ideal.leftAnnihilator`, `Ideal.rightAnnihilator`, and native ring-valued two-sided packaging;
   - `IsUnital.isStarProjection_coe_unit` and the focused backward refactor.
2. Ultraweak transport layer (completed on 2026-08-27):
   - closedness of annihilators;
   - algebra/opposite ultraweak homeomorphism.
3. Support layer (completed on 2026-08-27):
   - left/right support definitions and universal properties;
   - singleton-annihilator identities;
   - star compatibility and support of self-adjoint elements;
   - zero/one values, nonzero scalar invariance, and monotonicity on nonnegative elements.
4. Generated-algebra layer (completed on 2026-08-27):
   - nonunital ultraweak closure API;
   - internal unitality and commutativity preservation;
   - Sakai 1.10.4, proved through the existing ultraweakly closed corner API.
5. Central layer (completed on 2026-08-27):
   - Sakai 1.10.5;
   - central-projection/closed-two-sided-ideal order isomorphism;
   - central support and Sakai 1.10.7.
6. Lower spectral projection layer (completed on 2026-08-28):
   - `CStarAlgebra.spectralPositivePart`, its positive-part identity, nonnegativity, and norm
     continuity in the scalar cut;
   - `WStarAlgebra.spectralProjectionIio`, its leastness API, and monotonicity;
   - the least-upper-bound theorem and ultraweak continuity from below for arbitrary nonempty
     directed preorders, later upgraded downstream to exact strong left continuity;
   - cutoff recovery, commutation, spectral-band bounds, and the increment estimate of Sakai
     1.11.2;
   - the lower and upper endpoint formulas; their eventual constancy yields limits in any topology,
     including Sakai's strong topology, while named production limit theorems are ultraweak.
7. Finite spectral-sum layer (completed on 2026-08-28):
   - unbundled lower and upper sums for a real cut function and a finite number of adjacent bands;
   - self-adjointness and telescoping of band projections;
   - bracketing of the original element, the mesh-times-identity order bound, and norm error bounds
     for both sums.
8. Spectral approximation layer (completed on 2026-08-28):
   - filter-general convergence of lower and upper sums whenever the division endpoints contain
     the spectrum and the mesh bounds tend to zero;
   - canonical uniform dyadic divisions on
     `[-‖a‖ - 1, ‖a‖ + 1]`, with positivity, endpoint, width, refinement, and mesh-limit lemmas
     at seminormed additive star-group generality;
   - norm convergence of the concrete dyadic lower and upper sums to the original self-adjoint
     element.
9. Spectral-band theorem layer (completed on 2026-08-30):
   - ordered differences are projections;
   - bands commute with the element, lower projections, and one another;
   - adjacent additivity and orthogonality of ordered disjoint bands;
   - the underlying four-projection fact at nonunital $C^*$-algebra generality.
10. Tagged spectral-sum layer (completed on 2026-08-30):
   - endpoint-tag bridges to the established lower and upper sums;
   - self-adjointness, the lower/upper sandwich, and sharp gap/mesh estimates;
   - filter-general and dyadic norm convergence;
   - a named theorem passing the filter-general limit to every specified ultraweak topology.
11. Truncated-affine theorem layer (completed on 2026-08-30):
   - a partial-interval tagged estimate requiring no spectral endpoint exhaustion;
   - bandwise lower and upper bounds for `(r-a)⁺`, including the band crossing `r`;
   - a sharp mesh bound for arbitrary in-band truncated-affine tags;
   - filter-general norm convergence, specified-ultraweak convergence, and a dyadic corollary to
     the existing CFC-native `spectralPositivePart`.
12. Fixed-projection ultraweak decomposition layer (completed on 2026-08-30):
   - fixed-element extraction separates the limits of two pieces from the ultraweak limit of their
     difference;
   - a star projection plus eventual positivity identifies the limits with positive and negative
     parts, without asserting ultraweak continuity of positive part;
   - projection supports simplify canonically, and a strictly positive scalar projection lower
     bound implies inclusion in support;
   - source-faithful finite and conditional support/uniqueness scratch theorems isolate the sole
     remaining bridge without publishing a spectral-resolution structure.
13. Radon--Stieltjes refinement candidate layer (completed conditionally on 2026-08-30):
   - exact external audit of PNT+, teorth/analysis, pinned/current Mathlib, ICERM, and original
     LeanOA;
   - finite prescribed-cut cofinality by existing Mathlib `Finset`/`Ici` filter infrastructure;
   - canonical ordered finite-cut enumeration, asymptotic extrema, and maximum adjacent mesh;
   - a nontrivial filter combining inclusion refinement and mesh convergence, with endpoint escape
     and eventual-identity insertion of fixed cuts;
   - translated moment and endpoint-residual transport for arbitrary source filters;
   - complete pointwise and family uniqueness under the explicit candidate moment limit;
   - no public interface, because source equivalence remains unreviewed.
14. Strong spectral-continuity layer (completed on 2026-08-31):
   - projection ultraweak-to-strong convergence under eventual domination;
   - strong convergence of canonical directed projection LUB nets;
   - nested-projection strong-seminorm monotonicity;
   - filter-general strong left continuity of lower spectral projections;
   - the exact nonmonotone sequential statement of Sakai Lemma 1.11.1.
15. Section 1.12 production (begun at checkpoint
    `6d24a2feb704cae6e4bedc00d6bc9f17c601f310`, reviewed on 2026-08-31):
    - `CFC.abs_mul_eq_zero_iff` and `CFC.mul_abs_eq_zero_iff` at nonunital $C^*$-algebra
      generality;
    - `IsStarProjection.mul_star_mul_self`, `mul_star_mul_self_assoc`, and `mul_star_self`;
    - the exact regularized contractions, product identity, and norm limits of Sakai 1.12.1 checked
      in `Scratch/SakaiElementPolarRegularizer.lean`;
    - an audited handoff to the existing ultraweak compact closed ball and fixed-right-
      multiplication continuity, with no assumption of joint ultraweak continuity;
    - the independently reviewed W-star rewrites `WStarAlgebra.support_abs` and
      `support_abs_star`, downstream of the existing support API and the accepted annihilator
      equivalence;
    - WS-4 production existence via the exact ultraweak cluster and `q * b * p` cutdown route,
      with both source support equations and no public regularizer/predual implementation detail.
    - WS-5 algebraic uniqueness from only the factorization and initial supports;
    - exact `ExistsUnique` packaging and a checked public Verso node for Sakai 1.12.1.
16. Section 1.13 first production wave (begun at baseline
    `d19b0d77f71931add5f925a66156208ba7232425`):
    - exact bounded directed-positive normality through existing `ScottContinuousOn`;
    - intrinsic equivalence with projection normality and full Scott continuity;
    - exact specified-predual form of Sakai Theorem 1.13.2;
    - arbitrary-index orthogonal projection finite sums, monotonicity, projection/ambient LUBs,
      and ultraweak/strong convergence;
    - scratch `HasSum` semantics, forward complete additivity, and an exact converse reduction;
    - no complete-additivity predicate or converse promoted.
17. Section 1.13 second production wave (begun at baseline
    `9cd4ecf926b0fdd50a7c97a32fc9e80372a2e13d`, completed on 2026-09-01):
    - generic finite orthogonal-sum domination and commutation at a directed projection LUB;
    - a Zorn-maximal orthogonal decomposition of every nonempty projection chain, with finite sums
      dominated by chain members and supremum equal to the chain LUB;
    - chain-Scott cutoff, selection, and continuous-dual infrastructure, with existing normality
      APIs delegating to the weaker core;
    - normality implies arbitrary-universe orthogonal-family `HasSum`;
    - same-universe complete additivity implies canonical projection normality;
    - exact theorem-level iff, with no countability assumption, predicate, structure, or `tsum`.
18. Section 1.14.2 functional-support wave (begun at baseline
    `05c69abaa5a8608700a75d25b4da05d04d63a588`, completed on 2026-09-01):
    - a general positive-functional null left ideal and paired Cauchy--Schwarz coefficient lemmas;
    - exact strong closedness followed by the convex strong-to-ultraweak closure bridge;
    - the existing closed-left-ideal classifier and one intrinsic functional support definition;
    - right-annihilator, greatest-zero-projection, and all source cutdown identities;
    - full-support faithfulness and the explicitly derived faithful-support-corner theorems;
    - no duplicate element support, chosen-predual leak, normal-functional bundle, faithfulness
      predicate, or corner structure.
19. Section 1.14.1/1.14.3 orthogonal-Jordan wave (begun at baseline
    `ffb61d2e1abd8d5a66076762a43d0e2a90beafce`, completed on 2026-09-01):
    - Sakai's exact norm orthogonality at general nonunital $C^*$-algebra level;
    - the intrinsic support-product-zero characterization for normal positive functionals;
    - private splitting of the existing self-adjoint-unitary positive factorization by
      complementary projection cutdowns;
    - explicit normality, the exact difference and norm sum, and carrier-based uniqueness;
    - one source-facing `ExistsUnique` theorem, with no choice-based parts or second polar API;
    - independent mathematical/API review and an acyclic proof of the support equivalence.
20. Section 1.14.4 functional-polar wave (begun at baseline
    `ec16f22d31bca0b816eaf7f30f653ecdab5a5aae`, completed on 2026-09-01):
    - direct certification of Sakai's right-multiplication convention and both support
      orientations;
    - a single exposed-face extension downstream of the existing functional-factorization
      foundations, because the earlier public theorem covered only self-adjoint functionals;
    - exact pair uniqueness, normal positivity, norm preservation, and initial support;
    - canonical `Ultraweak.functionalAbs` introduced only after uniqueness;
    - normal positive conjugation and support transport proving the final projection
      `v * star v = s(|g⋆|)`;
    - no competing functional-polar namespace, partial-isometry predicate, support object, or
      chosen-predual leak in the intrinsic support bridge.

The source audit has closed the 1.11.3 review question with LEVEL C rather than an accepted
definition. Do not promote `atTop ⊓ comap divisionMesh (nhds 0)` as Sakai's meaning. Canonical
Lemma 1.11.1 is now source-formalized. Section 1.12 contains the single element
polar-decomposition theorem 1.12.1 and is complete through an independent
CFC/support/ultraweak-compactness chain followed by algebraic uniqueness. Section 1.13 is now
complete through the production projection-chain and complete-additivity modules. Section 1.14 is
complete through the general normal-functional polar decomposition of Theorem 1.14.4. The next
bounded transaction is a source/API audit of the five concrete operator topologies preceding
Proposition 1.15.1 and of Mathlib's current concrete-operator topology support. Revisit a public PVM/integral interface only
when coherent mathematics or new primary evidence fixes it.

Before each substantial proof, search the current Sak-AI tree, pinned Mathlib, current Mathlib
master/review history, and current LeanOA for an equivalent or more general declaration.

## Documentation continuation

The Verso package preserves all 87 active nodes and 141 statement-dependency edges in the generated
legacy graph and extends them to 121 nodes and 222 edges through the exact strong-topology,
fixed-projection, spectral-approximation, element-polar-decomposition, completed Section 1.13,
normal-positive-functional-support, norm-orthogonality, functional-Jordan, and general
functional-polar edges. The exact manifest count and audit state are recorded in
`VERSO_STATUS.md`. The legacy
sources remain recoverable from Git history. New mathematical documentation must be authored in
Verso first.

## Design gate

`REVIEW_QUEUE.md` contains a DESIGN REVIEW REQUEST about whether generalizing Mathlib's
`TwoSidedIdeal` to semirings should become an upstream project. This does not block the conservative
ring-valued implementation or the other work listed above.

## Required validation

After each implementation layer:

```sh
lake build <focused-module>
```

Before handoff:

```sh
lake build
lake lint
cd docs
lake build SakAIDocs
lake exe vbp build
lake exe vbp check
```

## External references

- Sakai scan: `/Users/jonbannon/Desktop/ClaudeMath/SakaiBook_1971.pdf` (read-only).
- Original LeanOA checkout: `/Users/jonbannon/LeanRepos/LeanOA` (read-only; do not alter).
- Current read-only upstream LeanOA comparison used in this run: commit `cb811c10`.
- Pinned Mathlib: commit `476ab284693e554a6b48c5f5210cb4fb5ae51252`.
- Mathlib master audited for Sections 1.12--1.13 on 2026-08-31:
  `be865aa50cc0364be66c3941a6dc0c845a2c2ceb`.
- Mathlib PR #42100 was still open at head `7f7138a127bf5c2f91d5b3e30b58499139561672`;
  its clopen-set CFC projections do not replace the W-star half-line support construction.
