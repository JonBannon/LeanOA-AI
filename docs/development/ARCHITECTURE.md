# Parallel-development architecture

This file operationalizes, but does not replace, the root `ARCHITECTURE.md` and the design contract.

## Layers and dependency direction

```text
Mathlib
  ↓
LeanOA/Mathlib staging (general, plausibly upstreamable gaps)
  ↓
functional analysis and C*-algebra infrastructure
  ↓
specified predual / ultraweak topology / W*-algebra bridges
  ↓
order, normality, projection, ideal, and support APIs
  ↓
Sakai theorem clusters (currently spectral resolution)
  ↓
Verso mathematical exposition and checked declaration links
```

The nested `docs/` package consumes the theorem package. It must never become a dependency of the
theorem package. Verso can reveal an awkward API, but foundational changes return to architecture
review rather than being designed independently in prose.

## Shared API policy

- GREEN APIs are safe downstream surfaces.
- YELLOW APIs may be consumed cautiously; do not expose their implementation details in new public
  interfaces.
- RED APIs have one architecture owner. Other streams state requirements rather than editing or
  replacing them.
- General facts go into `LeanOA/Mathlib/` only when their statement and namespace plausibly match
  Mathlib. Proof-local scaffolding stays private.
- Foundational representations, typeclass instances, and set-indexed spectral-resolution or
  integration objects require explicit review before adoption.

## Integration philosophy

The lead integrates in dependency order, checks design conformity before proof style, rejects
duplicate public foundations, and runs the full relevant build. Useful worker proofs may be retained
while their local wrappers are removed. Worktrees are disposable; accepted mathematics enters the
main branch only through reviewed commits.

The orchestration documents track work ownership and architecture only. Mathematical status and
dependency truth remain in Verso Blueprint blocks and `uses` references.

At the current Sakai 1.11.3 frontier, fixed-projection ultraweak decomposition is a reusable
downstream theorem layer. The source audit establishes that Sakai states the representation in his
strong `s(M,M_*)` topology, not the ultraweak topology, but leaves the integral's directed-division,
tag, refinement, and improper-endpoint semantics undefined. A scratch theorem checks the safe
topology-forgetting implication from strong convergence of the *same* finite-cut net to the
existing ultraweak conditional uniqueness chain. This does not certify that Sakai meant that net.
The resulting LEVEL C boundary does not authorize a public resolution, integral, or PVM
abstraction.

The exact canonical continuity theorem now lives in two downstream bridge modules:
`Ultraweak.StrongProjection` connects the existing projection lattice to the existing intrinsic
strong topology, and `Ultraweak.SpectralProjectionStrong` specializes that API to the lower
spectral family. This dependency direction is deliberate: neither foundational module imports the
other merely to host a bridge theorem. Sakai 1.11.1 is GREEN; the unrelated 1.11.3 integral
semantics remain RED.

Section 1.12 is complete through an independent CFC/support/ultraweak-compactness chain followed by
algebraic uniqueness. Element polar decomposition uses Mathlib `CFC.abs`, adds no duplicate
partial-isometry predicate, and lives in `Ultraweak.ElementPolarDecomposition`, distinct from the
existing functional `Ultraweak.PolarDecomposition` module.

Section 1.13 is a connective closeout rather than a new foundational normality layer. The
source-facing positive-directed bridge lives in `Ultraweak.NormalOrder`, downstream of the
canonical projection-normality/continuous-dual theorem. Arbitrary orthogonal projection sums live
in `Ultraweak.OrthogonalProjectionSum` as finite-subset/LUB/convergence theorems over the existing
projection subtype. `Ultraweak.ProjectionChain` supplies the minimal maximal-orthogonal
decomposition needed for the converse, while `Ultraweak.CompleteAdditivity` uses arbitrary-index
`HasSum` as its scalar semantics. Complete additivity remains theorem-level: no predicate or
parallel normality structure is public.

Section 1.14.2 adds functional support without changing the established element-support API.
`PositiveLinearMap.nullIdeal` is defined at the general unital $C^*$-algebra boundary, while
functional `PositiveLinearMap.support` is distinct from `WStarAlgebra.support` and requires an
explicit `IsNormalOnProjections` proof. Its chosen predual remains internal. Following Sakai's
dependency order, the null ideal is first proved closed in the intrinsic strong topology and then
ultraweakly closed through the existing convex strong-to-ultraweak closure theorem; the existing
closed-left-ideal classifier then supplies its unique projection generator. The faithfulness API
is theorem-level and reuses `IsStarProjection.Corner`: no `Faithful` predicate, normal-functional
bundle, null-support object, or competing corner structure is introduced. The next bounded
frontier is the orthogonal Jordan decomposition of self-adjoint normal functionals in 1.14.3.
