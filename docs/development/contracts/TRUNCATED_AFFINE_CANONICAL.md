# Workstream contract — canonical truncated-affine recovery

> **Read and obey `docs/development/SAKAI_DESIGN_CONTRACT.md` and the authoritative Sak-AI specifications it references. These requirements govern this workstream. Do not introduce designs inconsistent with them.**

## Objective

Develop the reusable partial-interval estimate and canonical convergence theorem for the weight
`lambda |-> (lambda_0 - lambda)^+`. The target must be the existing
`CStarAlgebra.spectralPositivePart`, hence Mathlib `cfc`, not a new integral or functional calculus.

## Ownership

- Scratch theorem development and one worker report in the isolated worktree.
- A proposed production module may be committed only if it contains theorem-level mathematics
  behind existing GREEN APIs and no experimental spectral-family structure.
- Do not edit Verso or shared coordination files.

## Required checks

- Inspect pinned Mathlib CFC/order/positive-part APIs before choosing target syntax.
- Handle a cutoff lying inside a partition interval; do not silently assume it is a cut.
- Prefer a reusable finite estimate, then norm convergence, then the existing norm-to-ultraweak
  bridge.
- Run focused Lean checks and scan for placeholders.
