# Sak-AI mathematical continuation

Last updated: 2026-08-28

## Verified repository state

- Branch: `master`.
- Base commit before the current finite-sum work: `d014439` (`feat: prove spectral family
  endpoints`).
- That commit contains the completed development through the endpoint part of Sakai 1.11.3.
- The theorem package had no uncommitted changes at the start of the current work.
- Jireh Loreaux's LeanOA and Mathlib are read-only references. The original LeanOA checkout has
  not been modified.

## Mathematical frontier

Sakai 1.10.3--1.10.7 is complete, and the spectral-resolution development now includes the
finite-partition estimate in Sakai 1.11.3: lower spectral projections are constructed, proved
monotone and ultraweakly continuous from below, satisfy Sakai's increment and endpoint formulas,
and yield lower and upper finite sums whose order and norm gaps are controlled by the mesh.

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

The next mathematical checkpoint is to choose a refining sequence of finite divisions whose mesh
tends to zero and prove that its lower and upper spectral sums converge in norm to the original
self-adjoint element. Re-audit the existing Sak-AI API first, then pinned/current Mathlib and the
read-only original LeanOA before choosing the refinement interface. Do not begin a completed
Radon--Stieltjes integration API or the uniqueness theorem prematurely.

Before each substantial proof, search the current Sak-AI tree, pinned Mathlib, current Mathlib
master/review history, and current LeanOA for an equivalent or more general declaration.

## Documentation continuation

The Verso package preserves all 87 active nodes and 141 statement-dependency edges in the generated
legacy graph and now has 96 nodes and 159 edges through the finite-partition estimate in Sakai
1.11.3. The exact audit and review state is recorded in `VERSO_STATUS.md`. The legacy sources remain
recoverable from Git history. New mathematical documentation must be authored in Verso first.

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
- Mathlib master observed on 2026-08-28: `8ce5b6b7138056305fda15c8360749f8a6b22c71`.
- Mathlib PR #42100 was still open at head `7f7138a127bf5c2f91d5b3e30b58499139561672`;
  its clopen-set CFC projections do not replace the W-star half-line support construction.
