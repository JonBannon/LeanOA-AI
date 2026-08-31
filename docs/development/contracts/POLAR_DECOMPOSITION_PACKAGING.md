# Workstream contract — Sakai 1.12.1 packaging and review

WORKSTREAM: Exact source theorem, uniqueness, and documentation

BASE COMMIT: assigned integration baseline after WS-4 existence equations compile; replace this
line with the exact WS-4 commit before dispatch

OBJECTIVE: Prove direct support-based uniqueness, expose the exact source-faithful `∃! u` theorem,
and integrate one Verso node for Sakai 1.12.1.

AMBIENT HYPOTHESES: retain exactly the ordinary established Sak-AI W-star context

```text
[CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] [WStarAlgebra M].
```

The chosen predual is internal. Do not add a public predual parameter, separability,
first-countability, sequential, or `Nontrivial M` assumption.

GOVERNING DESIGN DOCUMENTS:

> **Read and obey `docs/development/SAKAI_DESIGN_CONTRACT.md` and the authoritative Sak-AI specifications it references. These requirements govern this workstream. Do not introduce designs inconsistent with them.**

OWNED MODULES:

- `LeanOA/Ultraweak/ElementPolarDecomposition.lean`;
- a new `docs/SakAIDocs/Chapters/PolarDecomposition.lean` if the chapter split is retained;
- `docs/SakAIDocs/Blueprint.lean` and `docs/SakAIDocs/Chapters/Overview.lean`;
- `docs/development/reports/SAKAI_1_12_1_POLAR_DECOMPOSITION.md`;
- `docs/development/API_STATUS.md`, `docs/development/DEPENDENCY_MAP.md`,
  `docs/development/INTEGRATION_QUEUE.md`, `docs/development/WORKSTREAMS.md`, and
  `docs/development/VERSO_PLAN.md`;
- root `CONTINUATION.md` and `VERSO_STATUS.md`.

WS-5 starts only after WS-4 has stopped and its commit has been integrated; these streams must
never edit `ElementPolarDecomposition.lean` concurrently.

MAY DEPEND ON: the accepted factorization and initial/final support equations.

MUST NOT REDESIGN: partial-isometry semantics, CFC absolute value, support, or the existing
functional-polar-decomposition module. A noncomputable `polarPart` may be proposed only with an
immediate downstream consumer; it must not block the theorem.

TARGET RESULT: an exact unique-existence declaration whose predicate includes all three source
conditions

```text
a = u * CFC.abs a
star u * u = (support |a|).1
u * star u = (support |star a|).1,
```

with the two absolute values represented by their exact bundled `selfAdjoint M` terms. Prove
uniqueness from the factorization and support equations; do not replace the conjunction by a
stronger implementation-specific condition.

VALIDATION: full build, lint, Verso/vbp/site checks, `#print axioms`, placeholder scan, diff check.

STOP CONDITIONS: source hypotheses or uniqueness conditions have been changed, or packaging would
create an unnecessary competing abstraction.
