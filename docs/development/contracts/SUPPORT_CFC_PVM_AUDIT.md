# Workstream contract — support recovery and CFC/PVM architecture

> **Read and obey `docs/development/SAKAI_DESIGN_CONTRACT.md` and the authoritative Sak-AI specifications it references. These requirements govern this workstream. Do not introduce designs inconsistent with them.**

## Objective

Audit pinned/current Mathlib CFC architecture and test support recovery for the truncated-affine
CFC element, including the exact `Iio`/`Iic` and strict/non-strict endpoint convention. Assess how
a future PVM should induce the lower-family theorem layer without modifying CFC itself.

## Ownership

- Scratch proofs and private audit report in the isolated worktree.
- Current Mathlib and original LeanOA are read-only evidence.
- Do not edit production modules, Verso, or shared coordination files.

## Required checks

- Inspect the requested pinned CFC files by design role, not only theorem-name search.
- Distinguish norm-topological CFC construction from ultraweak convergence of approximants.
- Search for existing support/CFC bridges before proving local duplicates.
- State what survives unchanged under a future PVM and what remains RED.
- Run focused Lean checks for any proof evidence and scan for placeholders.
