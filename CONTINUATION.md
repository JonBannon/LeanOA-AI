# Sak-AI mathematical continuation

Last updated: 2026-08-31

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

The source audit has closed the 1.11.3 review question with LEVEL C rather than an accepted
definition. Do not promote `atTop ⊓ comap divisionMesh (nhds 0)` as Sakai's meaning. Canonical
Lemma 1.11.1 is now source-formalized. Section 1.12 contains the single element
polar-decomposition theorem 1.12.1 and is scoped as an independent, unblocked
CFC/support/ultraweak-compactness chain. The natural next bounded transaction runs the general
C-star partial-isometry/absolute-value API and the proof-local regularizer scratch test in parallel;
the W-star support bridge starts once the exact annihilator signatures are frozen. Revisit a public
PVM/integral interface only when coherent mathematics or new primary evidence fixes it.

Before each substantial proof, search the current Sak-AI tree, pinned Mathlib, current Mathlib
master/review history, and current LeanOA for an equivalent or more general declaration.

## Documentation continuation

The Verso package preserves all 87 active nodes and 141 statement-dependency edges in the generated
legacy graph and extends them to 103 nodes and 176 edges through the fixed-projection ultraweak
decomposition and the exact strong-topology continuity edge. The exact manifest counts and audit
state are recorded in `VERSO_STATUS.md`. The legacy
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
- Mathlib master audited for Section 1.12 on 2026-08-31:
  `be865aa50cc0364be66c3941a6dc0c845a2c2ceb`.
- Mathlib PR #42100 was still open at head `7f7138a127bf5c2f91d5b3e30b58499139561672`;
  its clopen-set CFC projections do not replace the W-star half-line support construction.
