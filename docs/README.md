# Sak-AI Verso documentation

This nested Lake package is the primary human-facing documentation source for Sak-AI. It is
separate from the theorem package so Verso's documentation dependencies do not alter the main
library's dependency resolution or default build.

The package follows the official `leanprover/verso-blueprint` project layout. Declaration links
are elaborated against the local parent package through `require LeanOA from ".."`, so renamed or
missing Lean declarations fail the documentation build.

## Build

```sh
cd docs
lake build SakAIDocs
lake exe vbp build
```

The generated multi-page site is `_out/site/html-multi/index.html`. Serve it over HTTP so the
search, hover, and graph assets can load:

```sh
python3 -m http.server 8000 -d _out/site/html-multi
```

The checked build must contain:

- `_out/site/html-multi/index.html`;
- `_out/site/html-multi/-verso-data/blueprint-manifest.json`;
- `_out/site/html-multi/-verso-data/blueprint-html-cache.json`.

The exact Verso Blueprint revision is pinned in `lakefile.toml` because the theorem package still
uses Lean `v4.32.0-rc1`. The direct `proofwidgets` and `plausible` pins deliberately match the
parent Mathlib manifest.

## VS Code

The theorem library and this documentation are separate Lake projects. Opening only the repository
root makes the Lean extension elaborate files in `docs/` against the theorem project's environment,
where the intentionally docs-only `Verso` dependency is unavailable.

Open [`Sak-AI.code-workspace`](../Sak-AI.code-workspace) with **File → Open Workspace from File…**.
Its two workspace folders give `LeanOA/` and `docs/` separate Lean language servers. If this project
was already open as a single folder, run **Lean 4: Restart File** after opening the workspace.

## Authoring layout

- `SakAIDocs/Blueprint.lean` assembles the book and generated global views.
- `SakAIDocs/Chapters/` contains the public mathematical and library reading paths.
- `SakAIDocsMain.lean` is the site generator entry point.

Development instructions and design-review policy are intentionally kept out of the public site.
They live in `../ARCHITECTURE.md`, `../STYLE_GUIDE.md`, and `../REVIEW_QUEUE.md` for the development
agent and human reviewers.

Keep the public `Current frontier` subsection in the project overview up to date until the
formalization program is complete.

All 87 active legacy LeanBlueprint nodes and 141 statement-dependency edges moved to Verso. The
development through Sakai 1.14.2 brings the current graph to 117 nodes and 209 edges, with 556
manifest/cache entries. Declaration links cover the Section 1.10,
spectral-approximation, fixed-projection, strong lower-spectral-projection, element-polar-
decomposition, source-normality, arbitrary orthogonal-projection-sum, projection-chain,
complete-additivity, and normal-positive-functional-support APIs. The legacy sources remain
available in Git history.
