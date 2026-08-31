# Workstream contract — Sakai Radon--Stieltjes representation bridge

**Read and obey `docs/development/SAKAI_DESIGN_CONTRACT.md` and the authoritative Sak-AI specifications it references. These requirements govern this workstream. Do not introduce designs inconsistent with them.**

Baseline: `0e5a79423227b11bf6100d0a641c4eca44057293` plus the coordination commit
that contains this contract.

Objective: reconstruct the weakest source-faithful Lean formulation of Sakai's strong-topology
Radon--Stieltjes representation and kernel-test how a refinement-directed identity-moment net,
asymptotic endpoints, and prescribed cuts produce the translated total and varying residual nets
consumed by the existing support-recovery scratch theorem.

Later source correction: the original workstream misread Latin `s` as Greek `σ`; its checked
ultraweak bridge is a topology-forgotten consequence, while the source's division semantics remain
LEVEL C ambiguous.

Owned output: scratch Lean and a focused worker report. Keep the lower family and its relation to
`a` as explicit terms/hypotheses. Coordinate with, but do not independently replace, the generic
division/refinement interface owned by the parallel stream.

Required checks: source topology; identity-weighted moment convention; left and right endpoint
residuals; insertion of `r` and `s<r`; translation by `r`; positivity/localization facts already
proved in finite scratch; precise use of cofinality; future PVM compatibility.

Forbidden: norm convergence, exact finite endpoint projections, support equality as an axiom,
positive-part continuity, a public integral/PVM/resolution structure, duplicate CFC, editing Verso
or shared coordination, pushing.

Commit the isolated result and distinguish kernel-checked implications from the remaining semantic
choice, if any.
