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
equations. The direct audit of Sakai Proposition 1.15.1 is complete. The proposition remains the
current source frontier: its exact proof needs the concrete $B(H)$ predual together with
$\sigma$-weak, ultrastrong, and relative-closure bridges. The first of these is now present in
Sak-AI, while the latter three are not. The library exposes
the canonical continuous identity from pointwise/SOT convergence to WOT and the corresponding
one-way closedness implication without conflating those missing topologies. It also constructs the
finite vector-functional span and proves that its induced weak topology is exactly Mathlib WOT;
the norm closure of that span is now certified as the concrete specified predual of $B(H)$ by a
general isometric duality theorem. The coefficient-series $\sigma$-weak, ultrastrong, and relative
closure bridges remain future work.

- [Sak-AI documentation site](https://jonbannon.github.io/Sak-AI/)
- [API documentation](https://jonbannon.github.io/Sak-AI/docs/)
- [Blueprint dependency graph](https://jonbannon.github.io/Sak-AI/Dependency-Graph/)
- [Formalization summary](https://jonbannon.github.io/Sak-AI/Blueprint-Summary/)
- [Upstreaming dashboard](https://jonbannon.github.io/Sak-AI/upstreaming.html)

The primary documentation source and deployed project site are the first-class Verso Blueprint
package in [`docs/`](docs/). It supplies a mathematical reading path, checked declaration links,
dependency graph, formalization summary, full-text search, and index. The retired LeanBlueprint
sources remain recoverable from Git history; all 87 former nodes and 141 dependency edges are in
Verso, whose current graph has 123 nodes and 223 statement-dependency edges. Exact build audit data
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
