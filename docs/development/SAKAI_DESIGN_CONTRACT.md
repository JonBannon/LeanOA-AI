# Sak-AI operational design contract

This is a short worker-facing summary of Sak-AI's existing design. It does not replace the
authoritative records named below. If this summary and an authoritative record disagree, stop the
affected work, record the discrepancy in `INTEGRATION_QUEUE.md`, and follow the authoritative
record unless the human maintainer decides otherwise.

## Authoritative sources

- [`ARCHITECTURE.md`](../../ARCHITECTURE.md): durable library and documentation decisions.
- [`STYLE_GUIDE.md`](../../STYLE_GUIDE.md): Lean, proof, naming, generality, and Verso practice.
- [`CONTINUATION.md`](../../CONTINUATION.md): current mathematical frontier and implementation
  order.
- [`REVIEW_QUEUE.md`](../../REVIEW_QUEUE.md): unresolved human design gates and upstream work.
- [`VERSO_STATUS.md`](../../VERSO_STATUS.md): documentation parity, validation, and next slice.
- [`README.md`](../../README.md), [`docs/README.md`](../README.md), `lakefile.toml`, and
  `.github/workflows/pages.yml`: operational build and deployment contract.
- Existing public declarations and recent accepted refactors are API evidence. Stale historical
  notes are not governing merely because they remain in Git history.

## Non-negotiable requirements

1. Sakai guides mathematical coverage and reading order; it does not dictate Lean names,
   abstraction boundaries, or proof architecture.
2. Target Mathlib-quality reusable APIs. Before adding a definition or theorem, search Sak-AI,
   pinned and current Mathlib, and the read-only original LeanOA. Reuse prior Sak-AI work as
   deliberately as upstream work.
3. Public declarations use the weakest natural assumptions that produce a recognizable reusable
   interface. Do not add ornamental typeclasses, and do not force scalar or nonunital generality
   where the mathematics is intrinsically narrower.
4. Put plausibly upstreamable general infrastructure in the mirrored `LeanOA/Mathlib/` hierarchy;
   put operator-algebra assembly in `LeanOA/`. Keep imports narrow and preserve dependency direction.
5. Prefer canonical Mathlib structures and bundled maps. Expose named bridge, application, coercion,
   extensionality, order, norm, and `simp` lemmas where they form a stable interface.
6. Treat definitional equality as an implementation detail. Clients cross semantic boundaries via
   named maps/equivalences or proposition-valued compatibility classes, not unfolding accidents.
7. Prove reusable mathematical estimates before bundling specialized constructions. Derive
   symmetric cases through existing equivalences, `star`, `flip`, or complements when natural.
8. Do not create parallel permanent foundations for local convenience. Shared representation,
   instance, topology, and foundational API choices require architecture/integration review.
9. Sak-AI introduces no custom mathematical axioms or proof placeholders. Never add `axiom`,
   `sorry`, `admit`, opaque declarations used as unproved assumptions, or equivalent mechanisms to
   fill a mathematical or source-semantics gap. Explicit theorem hypotheses are permitted only
   when they are genuinely part of the stated mathematics; they must not replace a proof from the
   weaker hypotheses claimed by the source. Standard Lean/Mathlib foundations are not custom
   Sak-AI axioms. Run textual placeholder/axiom scans at integration, and use `#print axioms` on
   principal new theorems when it helps audit their dependency chain.
10. Run Lean after substantive edits, `lake build` and `lake lint` for integration, and the
   documentation checks when Verso changes.
11. `LeanOA.lean` is the public umbrella. New public modules must be reachable from it.
12. Verso in `docs/` is the sole mathematical-documentation and theorem-status source. Do not create
   a second theorem-status ledger. `uses` edges and checked declaration links carry mathematical
   dependency and completion information.
13. Development policy stays out of the public mathematical reading path. Keep the public
   `Current frontier` section until the overall program is complete.
14. Generated documentation output is untracked and must not be edited or committed.
15. Human-facing prose uses $C^*$-algebra and $W^*$-algebra typography in new or substantially
   revised passages. Exact Lean identifiers retain their spelling. Any legacy typography migration
   must be systematic rather than scattered.
16. A locally compiling result is not integration-ready unless its statement is mathematically
   faithful, its abstraction fits the project, and it does not duplicate or leak unstable APIs.

## Parallel-work rule

Parallelize bounded theorem proving and implementation behind GREEN interfaces. Centralize shared
API design. A worker encountering a shared design choice records it in `INTEGRATION_QUEUE.md` and
continues only through a clearly temporary bridge that cannot become a competing public API.

Every workstream contract and worker prompt must include this sentence verbatim:

> **Read and obey `docs/development/SAKAI_DESIGN_CONTRACT.md` and the authoritative Sak-AI specifications it references. These requirements govern this workstream. Do not introduce designs inconsistent with them.**

## Validation commands

Theorem package:

```sh
lake build
lake lint
```

Documentation package:

```sh
cd docs
lake build SakAIDocs
lake exe vbp build
test -f _out/site/html-multi/index.html
test -f _out/site/html-multi/-verso-data/blueprint-manifest.json
test -f _out/site/html-multi/-verso-data/blueprint-html-cache.json
```
