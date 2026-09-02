# Sak-AI Verso status

Last updated: 2026-09-01

## Current state

The Verso Blueprint package in `docs/` builds and generates a multi-page site with 122 active nodes
and 222 statement-dependency edges. It includes all 87 nodes and 141 edges from the generated
legacy LeanBlueprint graph, the connected development through Sakai 1.14.4, and the finite
vector-functional WOT infrastructure at the current Section 1.15 frontier. The manifest has 576
entries and reports no unknown dependency references or missing external Lean declarations.

The apparent historical count of 88 came from counting textual `\label` occurrences: one of those
labels belongs to a fully commented-out proposal about recovering the norm from states. It was
never an active LeanBlueprint node and has no linked Lean declaration. Verso preserves it as
future-work prose rather than claiming it as a completed result.

The mathematical chapters now cover C-star and W-star foundations, order and projection lemmas,
positive functionals, Stonean spectra and real rank zero, normality and uniqueness of the predual,
Kaplansky density, the Section 1.10 support/central-support development, and lower spectral
projections through the exact strong-topology continuity theorem of Sakai 1.11.1, norm and
ultraweak convergence of arbitrary tagged spectral sums, and their truncated-affine recovery to
the existing CFC positive part in Sakai 1.11.3. It also presents the reusable fixed-projection
decomposition and the unique element polar decomposition of Sakai 1.12.1. The Section 1.13 chapter
now presents Sakai's exact bounded directed-positive normality condition, its equivalence with the
canonical projection-normality and specified-predual interfaces, and arbitrary-index orthogonal
projection finite sums together with their LUB, ultraweak convergence, and strong convergence. It
also presents the maximal orthogonal decomposition of projection chains and the exact
complete-additivity iff normality theorem, preserving arbitrary-cardinality semantics.
The functional-support chapter presents the GNS null left ideal, its source-order strong and
ultraweak closedness, the intrinsic support and greatest-zero characterization, all source cutdown
identities, global faithfulness, and the explicitly labeled derived faithful-support-corner
theorem. It now also presents Sakai's exact norm orthogonality, its support-product-zero
characterization, and the unique orthogonal Jordan decomposition of a self-adjoint normal
functional, including the exact norm sum. It now closes Section 1.14 with the unique general
normal-functional polar decomposition, canonical functional absolute value, norm identity, and
initial/final support equations.
The direct source and API audit for Proposition 1.15.1 is complete, but no source-theorem node for
that proposition has been added. Sakai's five conditions concern global closedness of a
self-adjoint subalgebra of $B(H)$, not equality of the topologies or a bounded-ball statement.
Pinned Mathlib supplies concrete WOT and pointwise/SOT, while Sak-AI supplies intrinsic predual
weak, strong, and Mackey topologies. A new infrastructure node records the proved fact that the
finite vector-functional span induces Mathlib WOT exactly and exhausts its continuous dual. The
norm-completed concrete predual, $\sigma$-weak coefficient-series, and ultrastrong identifications
required to join the remaining interfaces are still absent. The public document therefore
continues to identify Proposition 1.15.1 as the current source frontier rather than displaying a
false completion.
Scratch checks a nontrivial
refinement-plus-mesh filter and the complete competing-resolution support/uniqueness chain under an
explicit left-endpoint moment limit. The public document accurately stops before those candidate
results: source equivalence with Sakai's abstract Radon--Stieltjes integral has not been checked, so
they are not production theorems. Stable labels, theorem statements, proof sketches, declaration
links, and dependency edges cover the completed public frontier.

The legacy LeanBlueprint sources were removed after the parity and public-declaration audits. They
remain recoverable from Git history. Verso is the sole mathematical-documentation source.

The generated site includes a project overview with the current mathematical frontier, a
library/API path, interactive dependency graph, progress summary, full-text search, and index.
Agent-facing design and contribution instructions remain in the repository rather than the public
site. Generated output is intentionally ignored by Git.

## Validation

From `docs/`:

```sh
lake build SakAIDocs
lake exe vbp build
lake exe vbp check
test -f _out/site/html-multi/index.html
test -f _out/site/html-multi/-verso-data/blueprint-manifest.json
test -f _out/site/html-multi/-verso-data/blueprint-html-cache.json
```

All checks passed on 2026-09-01. `vbp check` reports `ok: true`, zero errors, and 576 manifest/cache
entries. The build replays warnings from three pinned upstream Verso or
SubVerso modules; Sak-AI's own documentation modules elaborate without warnings.

The theorem package also passes `lake build` and `lake lint`. The legacy documentation is no
longer part of the build or deployment.

## Exact continuation

1. Keep the Pages workflow green: it builds and lints the theorem library, builds doc-gen4 API
   documentation, builds and checks Verso, and deploys one combined static artifact.
2. Preserve the distinction now visible in the public chapter: canonical Lemma 1.11.1 is exactly
   source-formalized in `s(M,M_*)`, while the integral's division/refinement semantics remain LEVEL
   C ambiguous. Do not present the checked refinement-plus-mesh candidate as the source definition.
   Section 1.12's independent CFC/support/compactness proof and algebraic uniqueness theorem now
   supply exact Theorem 1.12.1. Section 1.13 is complete through source normality, arbitrary
   orthogonal projection sums, projection-chain decomposition, and theorem-level complete
   additivity. Section 1.14 is complete through functional
   support, exact norm orthogonality, its support characterization, and the unique orthogonal
   Jordan decomposition, followed by the exact general functional polar decomposition of Theorem
   1.14.4. The concrete operator-topology audit and finite coefficient/WOT bridge for Proposition
   1.15.1 are complete. The next bounded slice is the norm closure of that coefficient span and
   the isometric evaluation theorem certifying it as the concrete $B(H)$ predual. Proposition
   1.15.1 remains the source frontier until the resulting coefficient-series and ultrastrong
   identifications and the relative Kaplansky-closure step are kernel-proved. No resolution,
   integral, or PVM structure becomes public before a genuine mathematical interface fixes it.

Do not create a second theorem-status registry: Verso blocks and `uses` references are the
documentation source of truth.
