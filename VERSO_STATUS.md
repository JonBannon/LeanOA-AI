# Sak-AI Verso status

Last updated: 2026-08-31

## Current state

The Verso Blueprint package in `docs/` builds and generates a multi-page site with 108 active nodes
and 189 statement-dependency edges. This includes all 87 nodes and 141 edges from the generated
legacy LeanBlueprint graph plus twenty-one new connected nodes through the first production wave
for Sakai Section 1.13. The manifest has 515 entries and reports no
unknown dependency references or missing external Lean declarations.

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
projection finite sums together with their LUB, ultraweak convergence, and strong convergence.
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

All checks passed on 2026-08-31. `vbp check` reports `ok: true`, zero errors, and 515 manifest/cache
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
   supply exact Theorem 1.12.1. Section 1.13's source-normality bridge and arbitrary orthogonal
   projection sums are now public. The next bounded slice is the projection-chain decomposition and
   chain-LUB cutoff interface needed for the complete-additivity converse. The scratch `HasSum`
   formulation is not yet a public predicate. No resolution, integral, or PVM structure becomes
   public before a genuine mathematical interface fixes it.

Do not create a second theorem-status registry: Verso blocks and `uses` references are the
documentation source of truth.
