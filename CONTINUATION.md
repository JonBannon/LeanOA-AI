# Sak-AI mathematical continuation

Last updated: 2026-08-30

## Verified repository state

- Branch: `master`.
- Parallel orchestration began from `92db74d`; worker worktrees were cut from coordination commit
  `463d37e`.
- The first parallel spectral wave adds theorem-level band calculus and arbitrary tagged spectral
  sums without changing the lower spectral projection or choosing a spectral-measure object.
- The truncated-affine recovery transaction adds a theorem-only CFC bridge and leaves the
  arbitrary-resolution, PVM, and operator-valued integral boundaries explicitly RED.
- The theorem package had no uncommitted changes at the start of the orchestration work.
- Jireh Loreaux's LeanOA and Mathlib are read-only references. The original LeanOA checkout has
  not been modified.

## Mathematical frontier

Sakai 1.10.3--1.10.7 is complete, and the spectral-resolution development now includes norm
convergence of arbitrary tagged finite spectral sums in Sakai 1.11.3: lower spectral projections are
constructed, proved monotone and ultraweakly continuous from below, satisfy Sakai's increment and
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
    `WStarAlgebra.spectralProjectionIio` and prove Sakai 1.11.1 for arbitrary directed nets.
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
     directed preorders, specializing to Sakai 1.11.1;
   - cutoff recovery, commutation, spectral-band bounds, and the increment estimate of Sakai
     1.11.2;
   - the lower and upper endpoint formulas and their ultraweak limits from Sakai 1.11.3.
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

The next bounded architecture transaction is a source-faithful scratch test of the fixed-projection
ultraweak decomposition behind Sakai's uniqueness proof. Starting from asymptotic endpoint limits
and ultraweak identity-moment representation, allow an arbitrary cut `r` to be inserted and prove
the upper-support identity and strictly-below positive lower bounds. Do not replace these hypotheses
by exact finite endpoints or norm convergence, and do not publish a lower-family, resolution,
integral, or PVM structure until support recovery succeeds noncircularly.

Before each substantial proof, search the current Sak-AI tree, pinned Mathlib, current Mathlib
master/review history, and current LeanOA for an equivalent or more general declaration.

## Documentation continuation

The Verso package preserves all 87 active nodes and 141 statement-dependency edges in the generated
legacy graph and extends them to 102 nodes and 173 edges through canonical truncated-affine
recovery in Sakai 1.11.3. The exact manifest counts and audit state are recorded in
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
- Mathlib master observed on 2026-08-30: `e62ea4d7200989bad96e0cc05b349c1a5c9800c8`.
- Mathlib PR #42100 was still open at head `7f7138a127bf5c2f91d5b3e30b58499139561672`;
  its clopen-set CFC projections do not replace the W-star half-line support construction.
