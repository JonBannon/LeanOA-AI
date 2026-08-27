# Sak-AI mathematical continuation

Last updated: 2026-08-27

## Verified repository state

- Branch: `master`.
- Base commit before the current Verso work: `f4f36c4` (`Buildout of more Sakai`).
- That commit contains the completed Kaplansky density development and the 18-node Section 1.10
  chapter in the now-retired LeanBlueprint format.
- The theorem package had no uncommitted changes at the start of the current work.
- Jireh Loreaux's LeanOA and Mathlib are read-only references. The original LeanOA checkout has
  not been modified.

## Mathematical frontier

Sakai 1.10.3--1.10.7 is complete: support projections, the generated nonunital ultraweak algebra,
ultraweakly closed two-sided ideals, central support, and orthogonality of central supports.

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

The next mathematical task is to select a concrete endpoint in Sakai Section 1.11 and build its
Verso-first blueprint. Start by comparing Sakai's spectral-family construction with current
Mathlib's CFC/quasispectrum infrastructure and the active spectral-projection review work; do not
add a parallel spectral object when an upstream one is suitable.

Before each substantial proof, search the current Sak-AI tree, pinned Mathlib, current Mathlib
master/review history, and current LeanOA for an equivalent or more general declaration.

## Documentation continuation

The new Verso package has reached parity with all 87 active nodes and 141 statement-dependency
edges in the generated legacy graph; the exact audit and review state is recorded in
`VERSO_STATUS.md`. The extra textual legacy label is inside a fully commented-out future proposal
and was never an active graph node. A declaration-level audit also confirms that every named public
declaration added by the Section 1.10 development is linked or mentioned in Verso. The legacy
sources have therefore been retired and remain recoverable from Git history. New mathematical
documentation must be authored in Verso first.

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
- Current read-only upstream LeanOA comparison used in this run: commit `dd09e90`.
- Pinned Mathlib: commit `476ab284693e554a6b48c5f5210cb4fb5ae51252`.
- Mathlib master observed on 2026-08-27: `39c86ed8eb69c9ef854f1f2de1b7b7bd171fef15`.
