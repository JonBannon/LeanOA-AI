# Sak-AI architecture and design decisions

Last updated: 2026-08-31

## Theorem library

The package and public module namespace remain `LeanOA` for compatibility. Sakai supplies the
mathematical roadmap, but book numbering does not determine public Lean names or abstraction
boundaries. General algebraic and analytic infrastructure is staged in the mirrored `LeanOA.Mathlib`
hierarchy when it is plausibly upstreamable; domain assembly lives in the operator-algebra modules.

## Documentation architecture

The primary documentation source is a nested Lake package in `docs/` built with Verso's `Manual`
genre and `leanprover/verso-blueprint`. The nested package is deliberate:

- it isolates Verso's transitive dependencies from the theorem package;
- it imports the local parent package, so declaration links are checked against the working tree;
- it follows the current FLT/Verso Blueprint precedent for Mathlib-heavy formalization projects;
- it can evolve or be deployed without changing `lake build` for the theorem library.

The package pins Verso Blueprint commit `ae77d94f674f90ef7ca2303fdbeed2aba5e8f859`, the final
revision on its Lean `v4.32.0-rc1` line before that upstream branch moved to the stable compiler.
`proofwidgets` and `plausible` are pinned explicitly to the revisions used by the parent Mathlib.

The public site has four long-term surfaces: project overview, mathematical reading path,
library/API path, and formalization graph and summary. Search and the index are provided by Verso.
Development instructions and contribution policy stay in the repository-level agent-facing files,
not in the public reading path. Dependency data comes from `uses` references in the mathematical
exposition; there is no separately maintained theorem-status database.

While the formalization program remains incomplete, the project overview retains a public
`Current frontier` subsection. Update it when a milestone is completed or the next target changes;
remove it only when the overall program is finished.

## Documentation source of truth

The LeanBlueprint migration baseline was retired after exact parity was verified: 87 active nodes,
141 dependency edges, statement/proof exposition, and checked Lean declaration links. Its former
sources remain available in Git history. Verso is now the sole mathematical-documentation source;
new blueprint work must be authored there rather than in a parallel presentation layer.

CI builds the Verso site at the GitHub Pages root and preserves doc-gen4 API documentation under
`/docs/`. Generated HTML remains untracked and is assembled only locally or in CI.

## Generality and review

Public declarations use the weakest natural assumptions that create a recognizable reusable API.
Foundational representation choices, instance strategies, and proposed dependency refactors enter
the human review queue rather than being settled through a large local workaround.

## Parallel development

Operational multi-agent coordination lives in `docs/development/`.  Its design contract summarizes
this file, `STYLE_GUIDE.md`, `CONTINUATION.md`, `REVIEW_QUEUE.md`, and `VERSO_STATUS.md`; it does not
replace them.  Parallel streams may implement bounded mathematics behind stable interfaces, while
shared foundational API changes remain integration-owned.  Coordination records track ownership and
architecture only: Verso Blueprint blocks and `uses` references remain the sole mathematical-status
and theorem-dependency source.

## Spectral cutoffs and projections

For a fixed self-adjoint element, the scalar cutoff `(r • 1 - a)⁺` and its norm continuity live
in `LeanOA.CStarAlgebra.Spectral`; neither the declarations nor their import boundary depend on a
predual. Taking its support, proving projection-order properties, and proving ultraweak convergence
live in `LeanOA.Ultraweak.SpectralProjection`.

The intrinsic strong-topology bridge is deliberately downstream. General projection results live
in `LeanOA.Ultraweak.StrongProjection`, which imports both the established strong topology and the
projection lattice without reversing either foundational dependency. Exact strong left continuity
of the canonical lower spectral family lives in
`LeanOA.Ultraweak.SpectralProjectionStrong`. In particular, Sakai 1.11.1 is represented with no
extra monotonicity assumption; the older directed monotone theorem remains an ultraweak
consequence rather than the source theorem itself.

The lower projection is named `WStarAlgebra.spectralProjectionIio` rather than the unqualified
`spectralProjection`. The suffix records the half-line represented by the cutoff and reserves the
unqualified name for a future set-indexed spectral-measure interface compatible with Mathlib.

## Continuous calculus and a future PVM

Mathlib's `ContinuousFunctionalCalculus` is Sak-AI's canonical continuous calculus.
`CStarAlgebra.spectralPositivePart` is a source-facing name for its truncated-affine `cfc` value,
with named bridges to both `cfc` and positive-part notation. Sak-AI does not maintain a parallel
continuous functional calculus.

A future projection-valued measure and measurable spectral calculus form an additional layer. For
the spectral PVM of a self-adjoint element, restriction to strict lower half-lines should reproduce
`spectralProjectionIio`, and spectral integration should agree with Mathlib `cfc` on continuous
functions. PVM data, ultraweak representation, and measurable calculus do not become fields of the
CFC class. Until source-faithful support recovery for an arbitrary competing resolution is proved,
the lower-family, resolution, PVM, and operator-valued integral interfaces remain architecture-
owned RED boundaries; see `docs/development/DECISIONS/D003-spectral-resolution-cfc-pvm-architecture.md`.

## Central projections and closed two-sided ideals

Central projections are represented as a subtype of Mathlib's star-projection subtype with
membership in `Set.center`; ultraweakly closed two-sided ideals are a subtype of Mathlib's native
`TwoSidedIdeal`. Their order isomorphism is the connective API.

The complete lattice on central projections is built with `completeLatticeOfInf`, not by applying
`Equiv.completeLattice` to the order isomorphism. This deliberately reuses the existing subtype
`PartialOrder` definitionally and avoids an order-instance diamond. Central support is the infimum
of the central majorants; an annihilator classification supplies an actual least majorant, after
which its public closure-operator laws are order-theoretic.
