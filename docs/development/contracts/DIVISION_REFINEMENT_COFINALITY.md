# Workstream contract — finite divisions, refinement, and prescribed-cut cofinality

**Read and obey `docs/development/SAKAI_DESIGN_CONTRACT.md` and the authoritative Sak-AI specifications it references. These requirements govern this workstream. Do not introduce designs inconsistent with them.**

Baseline: `0e5a79423227b11bf6100d0a641c4eca44057293` plus the coordination commit
that contains this contract.

Objective: after auditing current Sak-AI and pinned Mathlib, kernel-test the smallest generic
finite-division/refinement layer needed to insert a finite set of prescribed real cuts, prove a
common-refinement/directedness result, prove cofinality of the prescribed-cut subsystem, and prove
generic preservation of `Tendsto` along the resulting cofinal map or filter.

Owned output: scratch Lean and a worker report in the isolated worktree. A production proposal is
allowed only for declarations that are genuinely general, Mathlib-style, not duplicated by the
external audit, and independent of spectral/CFC/PVM data. Keep any unreviewed type private or in
scratch.

Required stress tests: empty and singleton prescribed sets; duplicate cuts; endpoint preservation;
finite unions/common refinement; order orientation; nontriviality of the refinement filter; exact
relationship between `atTop`, `map`/`comap`, and cofinal restriction.

Forbidden: a spectral-resolution, PVM, integral, or mesh-only abstraction; exact endpoint
normalization; modifying Verso/shared coordination; pushing.

Commit the isolated result and report exact assumptions, public-API recommendation, and validation.
