# Sak-AI

Sak-AI is an AI-produced Lean operator-algebra project for private verification of results. Its
first long-term target is the development of Sakai's *C*-Algebras and *W*-Algebras*, followed by
the volumes of Takesaki. The current Lean library includes uniqueness of Banach preduals, Sakai's
Kaplansky density theorem, the Section 1.10 development through central-support orthogonality,
and lower spectral projections through norm convergence of the finite sums in Sakai 1.11.3. The
convergence theorem applies both to arbitrary mesh-zero filtered families and to an explicit
nested sequence of dyadic divisions. Sakai 1.11.1 is now formalized with its exact nonmonotone
hypotheses in the intrinsic strong topology. The source semantics of the abstract spectral integral
remain explicitly unresolved; the next independent checkpoint is the element polar decomposition
of Sakai 1.12.1.

- [Sak-AI documentation site](https://jonbannon.github.io/Sak-AI/)
- [API documentation](https://jonbannon.github.io/Sak-AI/docs/)
- [Blueprint dependency graph](https://jonbannon.github.io/Sak-AI/Dependency-Graph/)
- [Formalization summary](https://jonbannon.github.io/Sak-AI/Blueprint-Summary/)
- [Upstreaming dashboard](https://jonbannon.github.io/Sak-AI/upstreaming.html)

The primary documentation source and deployed project site are the first-class Verso Blueprint
package in [`docs/`](docs/). It supplies a mathematical reading path, checked declaration links,
dependency graph, formalization summary, full-text search, and index. The retired LeanBlueprint
sources remain recoverable from Git history; all 87 former nodes and 141 dependency edges are in
Verso, and the current graph has 103 nodes and 176 statement-dependency edges.

Local theorem verification:

```sh
lake build
lake lint
```

Local documentation verification and preview:

```sh
cd docs
lake build SakAIDocs
lake exe vbp build
lake exe vbp build --serve
```

The Pages workflow builds Verso from source, checks its generated manifest, combines it with the
Lean API documentation and upstreaming dashboard, and deploys the resulting static site.

The GitHub repository and project site use the Sak-AI name. The Lean package and module namespace
remain `LeanOA` for source compatibility while the Sakai development is extended.
