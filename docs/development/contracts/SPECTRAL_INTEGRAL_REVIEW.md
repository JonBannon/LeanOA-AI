# Workstream contract — spectral-integral prototype review

WORKSTREAM: Independent API and dependency review

BASE COMMIT: `397e006` plus the coordination-only transaction baseline

OBJECTIVE: Compare Candidate A and Candidate B against the design contract, current Sak-AI
spectral API, original LeanOA, and specifically relevant pinned/current Mathlib infrastructure.

GOVERNING DESIGN DOCUMENTS:

> **Read and obey `docs/development/SAKAI_DESIGN_CONTRACT.md` and the authoritative Sak-AI
> specifications it references. These requirements govern this workstream.**

OWNED FILES: a private review report in the assigned worktree only.

MAY DEPEND ON: read-only inspection of both prototype worktrees after they report ready.

MUST NOT REDESIGN: any public API or foundational type. Do not repeat the preceding Mathlib audit
mechanically; investigate only facts that distinguish the prototypes.

TARGET REVIEW: mathematical fidelity, genericity, topology visibility, uniqueness hypotheses,
refinement semantics, non-identity behavior, API collision risk, and the least missing abstraction.

EXPECTED PUBLIC API: none.

VALIDATION: cite exact declarations/files for material claims and distinguish proof evidence from
interface analysis.

