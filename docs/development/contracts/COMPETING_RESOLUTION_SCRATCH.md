# Workstream contract — arbitrary competing lower resolution

> **Read and obey `docs/development/SAKAI_DESIGN_CONTRACT.md` and the authoritative Sak-AI specifications it references. These requirements govern this workstream. Do not introduce designs inconsistent with them.**

## Objective

Replay truncated-affine weighted convergence for an arbitrary projection-valued lower family
`e'`, targeting the same Mathlib-CFC element as the canonical family. Replace canonical facts one
at a time by explicit hypotheses and record the minimum assumption ledger.

## Ownership

- Scratch files and one private worker report in the isolated worktree.
- Do not publish `LowerSpectralFamily`, `IsSpectralResolutionOf`, an integral predicate, a PVM, or
  any new typeclass.
- Do not edit production modules, Verso, or shared coordination files.

## Required checks

- Keep intrinsic-family, future-PVM-derived, resolution-of-`a`, CFC-native, and derived facts
  separate.
- Test explicit-parameter and predicate formulations before any bundling recommendation.
- Record a precise obstruction if the canonical theorem is not yet available or the assumptions
  become circular.
- Run focused Lean checks and scan for placeholders.
