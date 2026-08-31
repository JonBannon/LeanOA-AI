# Workstream contract — competing-resolution support recovery

**Read and obey `docs/development/SAKAI_DESIGN_CONTRACT.md` and the authoritative Sak-AI specifications it references. These requirements govern this workstream. Do not introduce designs inconsistent with them.**

Baseline: `162271ac17505779d1b2345ef5d4de434bf82c49` plus the coordination commit
that contains this contract.

Objective: in scratch space and with every hypothesis explicit, derive as much as possible of
support recovery for `x = CStarAlgebra.spectralPositivePart a r` from explicit ultraweak
approximation data for a competing monotone projection family `e`. Later source correction:
Sakai's literal topology is strong `s(M,M_*)`; this contract tests its topology-forgotten
consequence, not a source-faithful integral definition.

Targets in dependency order: `(e r).1 * x = x`; for every `s < r`, a strictly positive scalar
lower bound on `(e s).1`; use `IsLUB (e '' Set.Iio r) (e r)` to identify support; compare with
`spectralProjectionIio a r`; finish pointwise/family uniqueness if no substantive gap remains.

Reuse the generic scratch support criterion at `f5daad0` as evidence, but do not assume support
recovery or truncated-affine convergence as a resolution axiom. Keep Mathlib CFC as the target.

Forbidden: public resolution/PVM/integral structures, term-dependent typeclasses, support
continuity, norm strengthening, edits to Verso/shared coordination, or pushing.

Commit the isolated result and report exact proved hypotheses, blockers, and validation.
