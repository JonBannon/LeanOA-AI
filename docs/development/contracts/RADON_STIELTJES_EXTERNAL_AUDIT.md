# Workstream contract — external Riemann--Stieltjes audit

**Read and obey `docs/development/SAKAI_DESIGN_CONTRACT.md` and the authoritative Sak-AI specifications it references. These requirements govern this workstream. Do not introduce designs inconsistent with them.**

Baseline: `0e5a79423227b11bf6100d0a641c4eca44057293` plus the coordination commit
that contains this contract.

Objective: audit PNT+ (`AlexKontorovich/PrimeNumberTheoremAnd`), `teorth/analysis`, pinned and
current Mathlib, original LeanOA, and any directly implicated upstream source for reusable
division, refinement, prescribed-cut, cofinality, and Riemann--Stieltjes infrastructure.

Owned output: `docs/development/reports/RIEMANN_STIELTJES_EXTERNAL_AUDIT.md` in the isolated
worktree. Record exact repositories, commits, Lean/Mathlib revisions, licenses, files,
declarations, topology, endpoint convention, and one of the required reuse classifications.

Mandatory search includes repository history/branches/PRs where practical and the non-obvious
vocabulary listed in the transaction. Prefer primary source code and project metadata. Do not
infer operator-valued or ultraweak semantics from scalar/norm-topological names.

Forbidden: modifying production Lean, dependencies, Verso, or shared coordination files; adding an
external dependency; copying code without provenance; pushing.

Commit the isolated report and state which smallest coherent layer, if any, should be reused or
ported.
