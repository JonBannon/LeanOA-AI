# Sak-AI Verso status

Last updated: 2026-08-30

## Current state

The Verso Blueprint package in `docs/` builds and generates a multi-page site with 101 active nodes
and 169 statement-dependency edges. This includes all 87 nodes and 141 edges from the generated
legacy LeanBlueprint graph plus fourteen new connected nodes through norm and ultraweak convergence
of arbitrary tagged spectral sums in Sakai 1.11.3. The manifest has 471 entries and reports no
unknown dependency references or missing external Lean declarations.

The apparent historical count of 88 came from counting textual `\label` occurrences: one of those
labels belongs to a fully commented-out proposal about recovering the norm from states. It was
never an active LeanBlueprint node and has no linked Lean declaration. Verso preserves it as
future-work prose rather than claiming it as a completed result.

The mathematical chapters now cover C-star and W-star foundations, order and projection lemmas,
positive functionals, Stonean spectra and real rank zero, normality and uniqueness of the predual,
Kaplansky density, the Section 1.10 support/central-support development, and lower spectral
projections through norm and ultraweak convergence of arbitrary tagged spectral sums in Sakai
1.11.3. Stable labels,
theorem statements, proof sketches, declaration links, and dependency edges cover the completed
frontier.

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

All checks passed on 2026-08-30. `vbp check` reports `ok: true`, zero errors, and 471 manifest/cache
entries. The build replays warnings from three pinned upstream Verso or
SubVerso modules; Sak-AI's own documentation modules elaborate without warnings.

The theorem package also passes `lake build` and `lake lint`. The legacy documentation is no
longer part of the build or deployment.

## Exact continuation

1. Keep the Pages workflow green: it builds and lints the theorem library, builds doc-gen4 API
   documentation, builds and checks Verso, and deploys one combined static artifact.
2. Continue within Sakai 1.11.3 by scratch-testing a topology-explicit generic tagged-limit
   predicate against a spectral-family-specific `HasSpectralIntegral` proposition. Prove the two
   candidates equivalent for the identity integrand, but make no public choice before architecture
   review. Uniqueness remains a separate later clause.

Do not create a second theorem-status registry: Verso blocks and `uses` references are the
documentation source of truth.
