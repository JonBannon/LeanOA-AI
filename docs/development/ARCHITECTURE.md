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
downstream theorem layer. The remaining RED boundary is the semantics of an arbitrary competing
resolution's ultraweak Radon--Stieltjes representation, especially cofinal stability under
inserting prescribed cuts. Conditional support and uniqueness scratch theorems do not authorize a
public resolution, integral, or PVM abstraction before that bridge is fixed.
