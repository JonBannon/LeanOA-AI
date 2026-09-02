# Sakai Theorem 1.15.3 — trace-class architecture escalation

## What I was trying to prove

Continue from the source-checked statement of Sakai Theorem 1.15.3 to an independent
infinite-dimensional trace-class operator space and then prove the linear isometric identification

```text
a ↦ (x ↦ Tr(xa)) : T(H) ≃ₗᵢ B(H)_*,
```

including preservation and reflection of positivity, for an arbitrary complex Hilbert space.

## Current state

The exact theorem and its source prerequisites are recorded in
`SAKAI_1_15_3_SOURCE_AND_API.md`. The existing predual target is
`ContinuousLinearMap.VectorFunctionalPredual ℂ H H` and must not be replaced.

The common representation-neutral prerequisite is now kernel-proved in
`LeanOA.Mathlib.Analysis.InnerProductSpace.HilbertBasis`:

- arbitrary-index ENNReal operator energy;
- real and extended Parseval identities;
- equality for any explicit adjoint pair, without completeness assumptions;
- equality with Mathlib's adjoint energy;
- independence of the domain Hilbert basis;
- finiteness exactly when the real squared-norm family is summable.

No Hilbert--Schmidt, positive-trace, or trace-class carrier has been introduced.

## Why autonomous continuation stopped

This is escalation category **E3 — architectural fork**. Two honest designs are viable, and the
choice determines the public semantic core, module dependency order, and a large amount of later
operator-ideal API. The project constitution does not prefer one strongly enough to make that
durable choice autonomously.

## Evidence

Neither pinned Mathlib, audited current Mathlib, original LeanOA, nor current Sak-AI supplies an
infinite-dimensional Hilbert--Schmidt/trace-class/Schatten/nuclear-operator carrier or positive
operator trace. Mathlib's `LinearMap.trace` is finite-basis infrastructure and falls back to zero
outside that setting, so it cannot be reused for Sakai's theorem.

Sakai's source order builds Hilbert--Schmidt operators first, defines the positive trace by a
basis-diagonal sum, defines trace class by `Tr(|a|) < ∞`, and only then identifies it with the
coefficient predual. Sak-AI, however, already has a complete coefficient-predual, arbitrary-index
coefficient-series, multiplier, support, and element/functional polar-decomposition API. That
existing work makes a shorter range-first proof possible without defining trace class circularly.

## Options

### A. Hilbert--Schmidt first, following Sakai's construction order

Build the Hilbert--Schmidt carrier from finite `operatorEnergy`, its normed/Hilbert structure,
adjoint and two-sided ideal operations, completeness and compactness. Then construct positive
trace, trace class as `Tr(|a|) < ∞`, the trace norm, complex trace and cyclicity, and finally the
predual equivalence.

- **Mathematical consequence:** highest line-by-line source fidelity and a broad standard
  operator-ideal library before Theorem 1.15.3.
- **Architectural consequence:** the public semantic core is Hilbert--Schmidt-first.
- **Downstream effect:** strongest immediately reusable ideal API, but the longest route to the
  source theorem and substantial infrastructure not needed by its shortest proof.

### B. Source-faithful predual-range hybrid

First define the positive trace independently from basis-diagonal sums and define trace class by
the source condition `Tr(|a|) < ∞`. Recover from each existing coefficient-predual element the
bounded operator characterized by

```text
⟪η, Aₚ ξ⟫ = p(rankOne ξ η),
```

then use finite-basis compression, square-root coefficient series, predual multipliers, and the
existing element/functional polar decompositions to prove that this operator range is exactly the
independently defined trace class and that the norms and positive cones correspond. Build the
full Hilbert--Schmidt ideal afterward.

- **Mathematical consequence:** the statement remains source-faithful because trace class is
  defined independently; it is not a synonym for the predual.
- **Architectural consequence:** the first proof of Theorem 1.15.3 is organized around the
  already stable coefficient-predual API rather than a completed Hilbert--Schmidt ideal.
- **Downstream effect:** shortest honest route to the theorem and maximal reuse of Sak-AI, at the
  cost of differing from Sakai's construction order and postponing the full Hilbert--Schmidt
  Banach-ideal package.

The compact-positive spectral-sum route is not recommended as a primary option: current Mathlib
lacks the enumerated compact spectral expansion, and that route does not naturally supply the
trace-norm Banach ideal or cyclicity.

## Recommendation

Choose **B, the source-faithful predual-range hybrid**. It preserves the independent source
definition `Tr(|a|) < ∞`, reuses the substantial predual and polar-decomposition work already in
Sak-AI, and reaches the exact theorem without first building operator-ideal structure that the
proof does not consume. The Hilbert--Schmidt-first development can then be added as a reusable
characterization rather than as a gate.

## Exact question for the PI

Should Sak-AI use **A, Sakai's Hilbert--Schmidt-first semantic core**, or **B, the recommended
source-faithful predual-range hybrid**, for the permanent positive-trace and trace-class
architecture?
