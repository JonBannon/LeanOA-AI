# Integration queue

Only shared API, cross-stream, and design-contract questions belong here. Local proof problems stay
in their workstream.

## IQ-001 — spectral-resolution and integral interface

- **Status:** DEFERRED / RED — LEVEL C source ambiguity
- **Affected streams:** architecture, Mathlib reconnaissance, spectral bands, tagged sums, Verso
- **Question:** What future coherent PVM/integral construction, or new primary evidence, can fix a
  public representation object without assigning semantics to Sakai's undefined phrase by fiat?
- **Constraints:** preserve `spectralProjectionIio` half-line semantics; do not claim a general
  set-indexed projection-valued measure prematurely; keep finite sums usable as rewrite tools.
- **Evidence obtained:** `reports/MATHLIB_SPECTRAL_AUDIT.md` shows that Mathlib's vector-measure
  integral is norm/variation based, neither pinned nor current Mathlib has a general PVM, and the
  current archived Riemann--Stieltjes API is norm-topological. D002's scratch comparison proves the
  generic and spectral-specific predicates equivalent for every real integrand, not just the
  identity. Atom counterexamples rule out unrestricted mesh-only semantics for discontinuous
  weights, and the canonical-specific predicate cannot state Sakai's arbitrary competing
  resolution `e'`. The truncated-affine transaction now adds a sharp canonical theorem with an
  interior cutoff and the exact existing CFC target. An arbitrary monotone projection family also
  satisfies the corresponding finite positive-part identity under exact endpoint normalization,
  but passing to the target through `Filter.Tendsto.cfc` requires norm moment convergence, which is
  stronger than the topology-forgotten ultraweak representation used by the checked conditional
  argument. Support recovery additionally needs lower
  bounds, an upper-support identity, and continuity from below; support is not continuous under
  norm limits. The fixed-projection transaction now kernel-checks the exact finite cutoff algebra,
  the total-moment-only positive/negative decomposition, both support inequalities, the `Iio` LUB
  recovery, and pointwise/family uniqueness under explicit inserted-cut approximation data. The
  refinement transaction now proves the generic prescribed-cut restriction, a nontrivial concrete
  finite-cut filter combining inclusion refinement with shrinking adjacent mesh, asymptotic
  endpoint escape, and the full finite-set-to-support-to-family-uniqueness assembly. The remaining
  source audit then established that the printed topology is the stronger `s(M,M_*)` topology, not
  `σ(M,M_*)`. It also found no source or uniform period convention fixing the undefined integral's
  division/refinement/improper-limit semantics. The same-net strong-to-ultraweak implication is
  kernel-checked, but the overall source relation is LEVEL C / UNCLEAR.
- **Decision so far:** publish the canonical theorem layer only. Publish neither experimental
  integral predicate nor a lower-family, resolution, or PVM structure. Publish the general
  fixed-projection decomposition and coherent support helpers under D004. The architecture remains
  OPEN / RED at a documented historical ambiguity. The concrete filter and uniqueness theorem
  remain scratch-only and are labeled `TRANSLATED_CANDIDATE`, not `SOURCE_EQUIVALENCE_CHECKED`.
- **Next bounded action:** do not manufacture source equivalence. The independent Section 1.12
  CFC/support/compactness chain is now complete without touching this boundary. Continue with the
  Section 1.13 source-normality and orthogonal-sum closeout. Revisit a public representation
  predicate only when a coherent PVM/integral construction or new primary evidence fixes its
  semantics.

## IQ-002 — spectral helper generality

- **Status:** RESOLVED for the first wave
- **Affected streams:** spectral bands and tagged sums
- **Question:** Which interval-projection and tagged-sum facts are naturally generic for any
  monotone projection family, and which should remain specialized to `spectralProjectionIio`?
- **Default:** prove generic theorem-level facts where the assumptions stay recognizable; do not
  introduce a generic bundled spectral-family structure merely to share one proof.
- **Decision:** extract only the four-projection orthogonality fact to the nonunital Mathlib-staging
  layer. Keep spectral-band and tagged-sum declarations specialized to `spectralProjectionIio`,
  with named bridges showing that the existing lower and upper sums are endpoint-tag cases.

## IQ-003 — `TwoSidedIdeal` representation

- **Status:** HUMAN REVIEW; inherited from root `REVIEW_QUEUE.md`
- **Affected streams:** ideals, future upstreaming
- **Default:** preserve the existing native Mathlib object and its completed API. Do not implement
  the alternative representation in parallel.

## IQ-004 — orchestration versus theorem-status source

- **Status:** RESOLVED
- **Decision:** coordination files may track ownership, interface stability, and architectural
  dependencies, but Verso remains the only theorem-status/dependency registry.

## IQ-005 — element polar-decomposition packaging

- **Status:** RESOLVED / GREEN
- **Affected streams:** general C-star API, support, CFC regularizer, ultraweak compactness, Verso
- **Question:** Which reusable helper surface is needed before packaging Sakai 1.12.1?
- **Decision:** keep Mathlib `CFC.abs` canonical. The stable annihilator bridges are
  `CFC.abs_mul_eq_zero_iff` and `CFC.mul_abs_eq_zero_iff`; the stable partial-isometry consequences
  are `IsStarProjection.mul_star_mul_self`, `mul_star_mul_self_assoc`, and `mul_star_self`. Continue
  to express partial-isometry semantics through `IsStarProjection (star u * u)` initially; use a
  distinct future `Ultraweak.ElementPolarDecomposition` module so the existing functional-polar-
  decomposition module remains unambiguous. Do not add a `polarPart` object until a consumer needs
  one.
- **Evidence:** WS-4 privately productionizes the source-faithful regularizer, reuses the
  existing ultraweak compact closed ball and fixed-right-multiplication API, and kernel-proves the
  source cutdown `u = q * b * p`. `WStarAlgebra.exists_element_polar_decomposition` has the exact
  factorization and initial/final support orientations without a new support object, exposed
  predual, partial-isometry predicate, or joint-continuity assumption. The source consequence
  `CFC.mul_star_eq_of_eq_mul_abs` is stated at abstract nonunital real-CFC generality.
  WS-5 proves uniqueness using only the factorization, initial-support equations, and existing
  support zero-kernel theorem. The exact `ExistsUnique` declaration and Verso node are integrated.
- **Outcome:** no new `polarPart`, partial-isometry predicate, compactness layer, or public predual
  parameter. Sakai 1.12.1 is source-formalized.

## IQ-006 — Sakai 1.13 source normality and complete additivity

- **Status:** RESOLVED / GREEN
- **Affected streams:** positive functionals, projection lattice, strong projection convergence,
  predual uniqueness, Verso
- **Question:** How should Sakai's all-positive directed-supremum definition and arbitrary
  orthogonal-family complete additivity be connected to the existing projection-normality API?
- **Default:** do not add a competing permanent normality definition and do not use `tsum` for an
  arbitrary, possibly uncountable, projection family. State finite-partial-sum nets through
  `Finset`/`IsLUB` and reuse the existing projection lattice and convergence theorems.
- **Decision:** keep `IsNormalOnProjections` canonical. Express Sakai 1.13.1 through the existing
  bounded nonnegative `ScottContinuousOn` condition and prove all characterizations. Express the
  operator sum through `Finset` partial sums and the existing projection `iSup`, with no new
  structure or notation. Use arbitrary-index `HasSum` for future scalar complete additivity.
- **Evidence:** `Ultraweak.NormalOrder`, `Ultraweak.OrthogonalProjectionSum`,
  `Ultraweak.ProjectionChain`, and `Ultraweak.CompleteAdditivity` close all production branches.
  The maximal orthogonal chain decomposition, finite domination, LUB recovery, chain-LUB
  cutoff/selection route, and both implications are kernel-checked. The public surface is
  theorem-only: `HasSum` expresses the arbitrary finite-subsum limit and no new normality or
  complete-additivity predicate is needed.
- **Outcome:** the next source target, functional support in Sakai 1.14.2, was completed under
  IQ-007; see `reports/SAKAI_SECTION_1_14_SCOPE.md`.

## IQ-007 — Sakai 1.14.2 normal-positive-functional support

- **Status:** RESOLVED / GREEN
- **Affected streams:** positive functionals, intrinsic strong topology, one-sided ideals,
  element support, corners, future functional Jordan and polar decomposition
- **Question:** How should functional support be constructed without duplicating element support,
  normality, ideal classification, or corner infrastructure?
- **Decision:** define `PositiveLinearMap.nullIdeal` at general unital $C^*$-algebra level. Require
  an explicit `PositiveLinearMap.IsNormalOnProjections` proof for functional support, prove the
  null ideal strongly closed, obtain ultraweak closedness through the existing convex
  strong-to-ultraweak closure theorem, and reuse the existing closed-left-ideal classifier. Define
  `PositiveLinearMap.support` separately from `WStarAlgebra.support`, with the canonical $W^*$-
  predual hidden inside its construction.
- **Reusable helpers:** retain both Cauchy--Schwarz coefficient-zero orientations,
  `apply_star_mul_eq_zero_of_apply_star_mul_self_eq_zero_left` and
  `apply_star_mul_eq_zero_of_apply_star_mul_self_eq_zero_right`, together with the general
  ring/idempotent bridge `Ideal.mem_span_singleton_one_sub_iff_mul_eq_zero`.
- **Rejected alternatives:** no supremum-based second support, normal-positive-functional bundle,
  `Faithful` predicate, `Fact`-hidden normality, public null-support projection, or new corner
  structure. Use theorem-level faithfulness and `IsStarProjection.Corner`.
- **Outcome:** the Section 1.14.3 wave consumed this support API without redefining it; see IQ-008
  and `reports/SAKAI_1_14_1_1_14_3_JORDAN_DECOMPOSITION.md`.

## IQ-008 — Sakai 1.14.1 and 1.14.3 norm orthogonality and Jordan decomposition

- **Status:** RESOLVED / GREEN
- **Affected streams:** positive functionals, functional support, ultraweak factorization, corners,
  future functional polar decomposition
- **Question:** How should Sakai's norm orthogonality and the unique positive/negative
  decomposition of a self-adjoint normal functional be exposed without creating a second polar
  decomposition or premature choice-based parts?
- **Decision:** define `PositiveLinearMap.IsOrthogonal` by Sakai's norm formula at general
  nonunital $C^*$-algebra level. Reuse
  `Ultraweak.exists_positive_comp_mulLeft_of_isSelfAdjoint`, split its self-adjoint unitary
  privately into complementary projections, and use existing ultraweak corner cutdowns. Package
  the source theorem only as
  `Ultraweak.existsUnique_orthogonal_decomposition_of_isSelfAdjoint`.
- **Support boundary:** `PositiveLinearMap.isOrthogonal_of_support_mul_eq_zero` supplies the direct
  implication. The converse and
  `PositiveLinearMap.isOrthogonal_iff_support_mul_eq_zero` are derived after uniqueness, so support
  orthogonality characterizes but does not define the source relation.
- **Rejected alternatives:** no new normal-functional wrapper, Jordan-decomposition structure,
  public `positivePart`/`negativePart`, competing polar decomposition, or exposed carrier
  projection.
- **Outcome:** IQ-009 records the completed source-faithful general functional polar decomposition.

## IQ-009 — Sakai 1.14.4 general normal-functional polar decomposition

- **Status:** RESOLVED / GREEN
- **Affected streams:** positive functionals, normality, functional support, exposed faces,
  adjoint functionals, Verso
- **Question:** How should Sakai's arbitrary-normal-functional polar decomposition be exposed
  without mistaking the existing self-adjoint/left-action theorem for the source result or adding
  a parallel partial-isometry and absolute-value architecture?
- **Source decision:** use Sakai's right-action convention `g x = φ (x * v)`. Preserve norm
  equality, `star v * v = s(φ)`, uniqueness of the pair, and $v v^* = s(|g^*|)$ as explicit
  clauses.
- **Reuse decision:** keep `Ultraweak.PolarDecomposition` unchanged as the narrower self-adjoint,
  self-adjoint-unitary, left-multiplication factorization. Put the exact theorem downstream in
  `Ultraweak.FunctionalPolarDecomposition`, extending the same exposed-face method to the full unit
  ball and reusing `PositiveLinearMap.support`, support-nullity, cutdown, and existing ultraweak
  multiplication. Reuse the promoted normal pullback helper in both the Jordan and polar modules.
- **Shared API:** add nonunital `PositiveLinearMap.conjugate`; add normality preservation and
  `PositiveLinearMap.support_conjugate_eq_mul_star` downstream. Expose
  `Ultraweak.existsUnique_functional_polar_decomposition_basic`, then define the unique positive
  factor as `Ultraweak.functionalAbs` with its normality, specification, norm, and uniqueness
  lemmas. `Ultraweak.functional_polar_decomposition_final_projection` supplies the adjoint-support
  identity, and `Ultraweak.existsUnique_functional_polar_decomposition` is the exact source
  package.
- **Rejected alternatives:** no new `IsPartialIsometry` predicate; the initial-support equation
  already gives the established projection semantics. No normal-functional wrapper, second
  support, choice-based polar element, decomposition structure, or Jordan-derived surrogate
  statement. `functionalAbs` itself is deliberate because Sakai names the unique positive factor
  and the final-projection clause needs the support of the adjoint's absolute value.
- **Outcome:** Section 1.14 is complete. The next bounded action is a direct source/topology/API
  audit of Section 1.15 followed by Proposition 1.15.1.
