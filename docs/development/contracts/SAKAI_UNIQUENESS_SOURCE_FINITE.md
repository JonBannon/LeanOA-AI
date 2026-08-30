# Workstream contract — Sakai uniqueness source and finite decomposition

**Read and obey `docs/development/SAKAI_DESIGN_CONTRACT.md` and the authoritative Sak-AI specifications it references. These requirements govern this workstream. Do not introduce designs inconsistent with them.**

Baseline: `162271ac17505779d1b2345ef5d4de434bf82c49` plus the coordination commit
that contains this contract.

Objective: reconstruct the exact source hypotheses and proof of the uniqueness clause in Sakai
Theorem 1.11.3, then kernel-check the finite projection/band identities obtained by inserting an
arbitrary cutoff `r` into a division of an explicit monotone projection family.

Owned output: scratch Lean only, a source/finite-decomposition worker report, and no production
structure. Record exact PDF pages and distinguish quoted source content from reconstruction.

Required checks: strict `Iio` and `[r,s)` endpoint conventions; bands below/above the inserted cut;
left/right multiplication identities; which facts use projection-valuedness, monotonicity,
continuity from below, endpoint limits, or representation of `a`.

Forbidden: publishing `LowerSpectralFamily`, `IsSpectralResolutionOf`, a PVM, an integral, or a
term-dependent typeclass; replacing ultraweak hypotheses by norm convergence or exact endpoints;
editing Verso or shared coordination files; pushing.

Commit the isolated result and report exact validation and any source ambiguity.
