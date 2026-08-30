# Workstream contract — generic spectral-integral scratch prototype

WORKSTREAM: Generic tagged-partition limit predicate

BASE COMMIT: `397e006` plus the coordination-only transaction baseline

OBJECTIVE: Prototype Candidate A in disposable scratch space: a topology-explicit generic notion
of convergence of tagged finite sums, then stress-test whether it represents reusable mathematics
rather than a renamed `Filter.Tendsto`.

GOVERNING DESIGN DOCUMENTS:

> **Read and obey `docs/development/SAKAI_DESIGN_CONTRACT.md` and the authoritative Sak-AI
> specifications it references. These requirements govern this workstream.**

OWNED FILES: scratch Lean files and a private worker report in the assigned worktree only.

MAY DEPEND ON: Mathlib filters/topology/finite sums and the GREEN Sak-AI tagged spectral-sum API
for the identity specialization test.

MUST NOT REDESIGN: spectral projections, specified preduals, operator-valued measures, PVMs, or
public integration infrastructure.

TARGET TESTS: explicit partition/tag/sum/topology data; identity specialization; constants, steps,
affine combinations, interval restriction, refinement/mesh, uniqueness, and ultraweak
specialization.

EXPECTED PUBLIC API: none. Any independently natural lemma must be proposed to the integration
lead and separately reviewed before publication.

VALIDATION: focused Lean checks in the worktree; no placeholders in results claimed proved.

STOP CONDITIONS: the prototype becomes merely a wrapper around `Tendsto`, or requires a large
partition hierarchy unsupported by current mathematics.

