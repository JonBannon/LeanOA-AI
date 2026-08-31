# Sak-AI Verso status

Last updated: 2026-08-30

## Current state

The Verso Blueprint package in `docs/` builds and generates a multi-page site with 103 active nodes
and 175 statement-dependency edges. This includes all 87 nodes and 141 edges from the generated
legacy LeanBlueprint graph plus sixteen new connected nodes through the fixed-projection
ultraweak decomposition used in Sakai 1.11.3. The manifest has 492 entries and reports no
unknown dependency references or missing external Lean declarations.

The apparent historical count of 88 came from counting textual `\label` occurrences: one of those
labels belongs to a fully commented-out proposal about recovering the norm from states. It was
never an active LeanBlueprint node and has no linked Lean declaration. Verso preserves it as
future-work prose rather than claiming it as a completed result.

The mathematical chapters now cover C-star and W-star foundations, order and projection lemmas,
positive functionals, Stonean spectra and real rank zero, normality and uniqueness of the predual,
Kaplansky density, the Section 1.10 support/central-support development, and lower spectral
projections through norm and ultraweak convergence of arbitrary tagged spectral sums and their
truncated-affine recovery to the existing CFC positive part in Sakai 1.11.3. It now also presents
the reusable fixed-projection decomposition. Scratch now checks a nontrivial
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

All checks passed on 2026-08-30. `vbp check` reports `ok: true`, zero errors, and 492 manifest/cache
entries. The build replays warnings from three pinned upstream Verso or
SubVerso modules; Sak-AI's own documentation modules elaborate without warnings.

The theorem package also passes `lake build` and `lake lint`. The legacy documentation is no
longer part of the build or deployment.

## Exact continuation

1. Keep the Pages workflow green: it builds and lints the theorem library, builds doc-gen4 API
   documentation, builds and checks Verso, and deploys one combined static artifact.
2. Record the completed source audit faithfully: Sakai uses `s(M,M_*)`, while the integral's
   division/refinement semantics are LEVEL C ambiguous. Do not present the checked
   refinement-plus-mesh candidate as the source definition. The next public documentation slice
   should add the canonical strong-topology conclusion when it is proved, then move into Section
   1.12 where only established canonical conclusions are required. No resolution, integral, or PVM
   structure becomes public before a genuine mathematical interface fixes it.

Do not create a second theorem-status registry: Verso blocks and `uses` references are the
documentation source of truth.
