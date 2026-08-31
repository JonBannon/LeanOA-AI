# Workstream contract — Sakai 1.12 regularizer

WORKSTREAM: Section 1.12 regularized contractions

BASE COMMIT: `f840ec2643a255cf1fcbb5c69da316c74417829f`

OBJECTIVE: Kernel-check Sakai's regularization while translating its `n = 1, 2, ...` indexing to a
nondegenerate Lean `ℕ`-sequence. Set

```text
ε n    := ((n + 1 : ℝ)⁻¹)
c n    := star a * a + ε n • (1 : M)
h n    := CFC.sqrt (c n)
aReg n := a * (c n) ^ (-(1 / 2 : ℝ)).
```

This is Sakai's sequence indexed from `1`, reindexed over Lean's naturals.

GOVERNING DESIGN DOCUMENTS:

> **Read and obey `docs/development/SAKAI_DESIGN_CONTRACT.md` and the authoritative Sak-AI specifications it references. These requirements govern this workstream. Do not introduce designs inconsistent with them.**

OWNED MODULES:

- `Scratch/SakaiElementPolarRegularizer.lean`;
- `docs/development/reports/POLAR_DECOMPOSITION_REGULARIZER.md`.

Keep all sequence definitions in scratch initially. Propose production-local helpers only after
their signatures and independent reuse have been reviewed.

MAY DEPEND ON: pinned Mathlib `CFC.abs`, sqrt/rpow, strict positivity, inverse, order, and
conjugation APIs; accepted GREEN helpers already present at the base commit. When WS-3 runs in
parallel with WS-1, it must not import or copy any in-flight WS-1 declaration; the regularizer is
mathematically independent of that branch.

MUST NOT REDESIGN: continuous functional calculus or absolute value. Do not expose proof-specific
sequences as public definitions without an independent consumer.

TARGET RESULTS: prove the exact noncommutative identity

```text
star (aReg n) * aReg n =
  (c n) ^ (-(1 / 2 : ℝ)) * (star a * a) * (c n) ^ (-(1 / 2 : ℝ)),
```

and, if useful, rewrite the right side through single-element CFC commutativity as
`(star a * a) * Ring.inverse (c n)`. Do not use informal division notation as the formal target.
Also prove `‖aReg n‖ ≤ 1`, `aReg n * h n = a`, norm convergence
`h n → CFC.abs a`, and the norm convergence `aReg n * CFC.abs a → a` needed by WS-4.

HANDOFF TO WS-4: scratch is evidence, never a production dependency. After review, the lead must
freeze the accepted signatures and either (a) transplant the proof-local definitions and checked
proofs as private declarations into WS-4's production module, or (b) promote independently reusable
lemmas to a narrowly named production module. Production code must not import `Scratch`.

VALIDATION: scratch kernel check, focused build if promoted, no placeholders.

STOP CONDITIONS: a route requires a parallel calculus, silently assumes commutativity outside the
single-element CFC range, treats `0⁻¹` as Sakai's first regularization parameter, or ceases to reduce
the compactness proof.
