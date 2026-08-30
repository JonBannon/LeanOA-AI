# Workstream contract — spectral-specific integral scratch prototype

WORKSTREAM: Spectral-family-specific `HasSpectralIntegral`

BASE COMMIT: `397e006` plus the coordination-only transaction baseline

OBJECTIVE: Prototype Candidate B in disposable scratch space using only the spectral-family,
spectral-band, tagged-sum, and specified-ultraweak structures Sak-AI actually possesses.

GOVERNING DESIGN DOCUMENTS:

> **Read and obey `docs/development/SAKAI_DESIGN_CONTRACT.md` and the authoritative Sak-AI
> specifications it references. These requirements govern this workstream.**

OWNED FILES: scratch Lean files and a private worker report in the assigned worktree only.

MAY DEPEND ON: GREEN `SpectralProjection`, `SpectralBand`, `SpectralSum`,
`SpectralApproximation`, and `TaggedSpectralSum` APIs.

MUST NOT REDESIGN: spectral projections, specified preduals, operator-valued measures, PVMs, or
public integration infrastructure.

TARGET TESTS: a non-identity weighted tagged sum; identity equivalence with Candidate A; constants,
aligned step functions, affine combinations, interval restriction, refinement/mesh, uniqueness,
existing tagged-sum compatibility, and explicit specified-ultraweak convergence.

EXPECTED PUBLIC API: none. Experimental names must remain outside public imports and Verso.

VALIDATION: focused Lean checks in the worktree; no placeholders in results claimed proved.

STOP CONDITIONS: a stable definition requires a set-indexed PVM, a general measurable functional
calculus, or a canonical tagged-division filter not yet present.

