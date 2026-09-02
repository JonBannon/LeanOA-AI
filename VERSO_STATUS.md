# Sak-AI Verso status

Last updated: 2026-09-02

## Current state

The Verso Blueprint package in `docs/` builds and generates a multi-page site with 129 active nodes
and 238 statement-dependency edges. It includes all 87 nodes and 141 edges from the generated
legacy LeanBlueprint graph, the connected development through Sakai 1.14.4, Proposition 1.15.1,
and the weak-family clause of Proposition 1.15.2.
The manifest and HTML cache each have 624 entries, including 384 unique linked Lean declarations,
and report no unknown dependency references or missing external Lean declarations.

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
Proposition 1.15.1 is source-formalized by an exact five-way global closedness theorem for a
possibly nonunital self-adjoint subalgebra of $B(H)$. Its proof keeps concrete WOT,
coefficient-series sigma-WOT, pointwise/SOT, concrete ultrastrong convergence, and the intrinsic
concrete-predual ultraweak topology distinct; it does not claim their global equality. The
relative Kaplansky unit-ball theorem and scalar normalization supply the difficult reverse
implication.

Proposition 1.15.2 is the current numbered frontier. Its weak-family clause is source-formalized:
the canonical quotient-predual topology of a WOT-closed subalgebra, coefficient-series sigma-WOT,
and WOT agree on every zero-centered norm-closed ball. The reusable foundation first identifies
the quotient-predual weak-star topology of an arbitrary ultraweakly closed submodule with its ambient
ultraweak subspace topology at real- or complex-like scalar generality. Canonical homeomorphisms
and arbitrary-filter corollaries then give the source result. The strong-family clause remains
unformalized, so the full proposition is not marked complete and no global topology equality is
claimed.
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

All checks passed on 2026-09-02. `vbp check` reports `ok: true`, zero errors, and 624 manifest/cache
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
   1.14.4. Proposition 1.15.1 is source-formalized, and Proposition 1.15.2(1) is source-formalized
   on every norm-closed ball through the explicit quotient predual, canonical homeomorphisms, and
   arbitrary-filter convergence. The next bounded slice is the positive-square strong-family
   clause of Proposition 1.15.2. No resolution, integral, or PVM structure becomes public before
   a genuine mathematical interface fixes it.

Do not create a second theorem-status registry: Verso blocks and `uses` references are the
documentation source of truth.
