# Sak-AI

Sak-AI is an AI-produced Lean operator-algebra project for private verification of results. Its
first long-term target is the development of Sakai's *C*-Algebras and *W*-Algebras*, followed by
the volumes of Takesaki. The current Lean library includes uniqueness of Banach preduals, Sakai's
Kaplansky density theorem, the Section 1.10 development through central-support orthogonality,
and lower spectral projections through norm convergence of the finite sums in Sakai 1.11.3. The
convergence theorem applies both to arbitrary mesh-zero filtered families and to an explicit
nested sequence of dyadic divisions. Sakai 1.11.1 is now formalized with its exact nonmonotone
hypotheses in the intrinsic strong topology. The source semantics of the abstract spectral integral
remain explicitly unresolved. Sakai's element polar decomposition is now kernel-proved with exact
existence, algebraic uniqueness, and initial/final support equations, completing Theorem 1.12.1.
Section 1.13 now identifies Sakai's bounded directed-positive normality with the existing
projection-normality and predual APIs, proves arbitrary-index orthogonal projection finite-sum
convergence, and characterizes normality by complete additivity on arbitrary orthogonal projection
families. The converse is genuinely arbitrary-cardinal: a maximal orthogonal decomposition
recovers the least upper bound of every projection chain. Section 1.14.2 now constructs the support
of a normal positive functional from its null left ideal and proves the greatest-zero-projection,
cutdown, and faithfulness interfaces. Sakai's norm orthogonality and the unique orthogonal Jordan
decomposition of a self-adjoint normal functional are now formalized through Theorem 1.14.3.
Theorem 1.14.4 completes Section 1.14 with the unique polar decomposition of an arbitrary normal
functional, including its canonical absolute value, norm identity, and initial/final support
equations. Sakai Proposition 1.15.1 is now source-formalized: global closedness in WOT,
coefficient-series $\sigma$-WOT, SOT, concrete ultrastrong convergence, and the concrete-predual
ultraweak topology is equivalent for a possibly nonunital self-adjoint subalgebra of $B(H)$.
The weak-family clause of Proposition 1.15.2 is also source-formalized. For a WOT-closed such
subalgebra, its canonical quotient-predual topology, coefficient-series $\sigma$-WOT, and WOT
agree on every zero-centered norm-closed ball, with canonical homeomorphisms and arbitrary-filter
convergence corollaries. The proposition remains the current source frontier because its
strong-family clause—comparing intrinsic strong, concrete ultrastrong, and SOT on bounded
balls—still requires the positive-square bridge. No global equality of these topologies is
claimed.

- [Sak-AI documentation site](https://jonbannon.github.io/Sak-AI/)
- [API documentation](https://jonbannon.github.io/Sak-AI/docs/)
- [Blueprint dependency graph](https://jonbannon.github.io/Sak-AI/Dependency-Graph/)
- [Formalization summary](https://jonbannon.github.io/Sak-AI/Blueprint-Summary/)
- [Upstreaming dashboard](https://jonbannon.github.io/Sak-AI/upstreaming.html)

The primary documentation source and deployed project site are the first-class Verso Blueprint
package in [`docs/`](docs/). It supplies a mathematical reading path, checked declaration links,
dependency graph, formalization summary, full-text search, and index. The retired LeanBlueprint
sources remain recoverable from Git history; all 87 former nodes and 141 dependency edges are in
Verso, whose current graph has 129 nodes and 238 statement-dependency edges. Exact build audit data
is recorded in [`VERSO_STATUS.md`](VERSO_STATUS.md).

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
