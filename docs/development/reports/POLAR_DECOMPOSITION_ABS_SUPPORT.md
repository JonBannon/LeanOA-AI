# Polar-decomposition absolute-value support bridge

Date: 2026-08-31

Workstream: WS-2, Sakai Section 1.12

Baseline: `6d24a2feb704cae6e4bedc00d6bc9f17c601f310`

## Scope and outcome

This workstream adds the thin $W^*$-algebra bridge from Mathlib's canonical `CFC.abs` to Sak-AI's
existing one-sided support projections.  It introduces no new support object, partial-isometry
predicate, normality hypothesis, predual data, or functional calculus.

The production surface consists of exactly the two identities needed to state Sakai's polar
decomposition with the established support orientations.

## Overlap and dependency audit

The audit searched by declaration name and mathematical content in:

- Sak-AI at baseline `6d24a2feb704cae6e4bedc00d6bc9f17c601f310`;
- pinned Mathlib at `476ab284693e554a6b48c5f5210cb4fb5ae51252`;
- the current-Mathlib comparison recorded by the accepted WS-1 audit at
  `567908cf509fb0bab796e5401edf35b4492ae48f`;
- the read-only original LeanOA checkout at
  `cb811c1006ae78a0ff1d175253200e1859843370`.

No existing theorem identifies the support of `CFC.abs a` with either one-sided support of `a`.
The implementation reuses rather than duplicates:

- `CFC.abs_mul_eq_zero_iff`, the accepted nonunital $C^*$-algebra annihilator bridge from WS-1;
- `WStarAlgebra.rightSupport_le_iff`, the least-projection characterization of right support;
- `WStarAlgebra.mul_rightSupport`, the right-support identity;
- `IsSelfAdjoint.leftSupport_eq_rightSupport`, which identifies the two supports of a
  self-adjoint element;
- `WStarAlgebra.rightSupport_star`, which exchanges right and left support under adjoint.

In particular, the proof does not unfold support projections, annihilator ideals, or their
ultraweak construction.

## Added declarations

The new module `LeanOA.Ultraweak.AbsSupport` exposes:

```lean
@[simp] theorem WStarAlgebra.support_abs (a : M) :
  WStarAlgebra.support
      ⟨CFC.abs a, (CFC.abs_nonneg a).isSelfAdjoint⟩ =
    WStarAlgebra.rightSupport a

theorem WStarAlgebra.support_abs_star (a : M) :
  WStarAlgebra.support
      ⟨CFC.abs (star a), (CFC.abs_nonneg (star a)).isSelfAdjoint⟩ =
    WStarAlgebra.leftSupport a
```

Both declarations assume exactly the ambient support-layer interface

```lean
[CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] [WStarAlgebra M].
```

There is no explicit choice of predual and no assumption that `a` is normal.  The $W^*$-algebra
boundary is intrinsic to the existing support construction; the annihilator fact used inside the
proof remains at its more general nonunital $C^*$-algebra boundary.

The `support_abs` simp attribute has a canonical normal-form direction: a bundled support of an
absolute value reduces to the already established one-sided support of the original element.
`support_abs_star` is intentionally not another simp lemma, because it is already the composite
normal form produced by `support_abs` and `rightSupport_star`; the named result remains useful as
the exact source-facing orientation.

## Proof and orientation audit

For the first theorem, self-adjointness changes `support (CFC.abs a)` to
`rightSupport (CFC.abs a)`.  The two projection inequalities then follow from
`rightSupport_le_iff`.  Each required right-identity is obtained by multiplying the complementary
projection, transferring the zero product through `CFC.abs_mul_eq_zero_iff`, and using the
corresponding existing right-support identity.

The starred theorem is deliberately derived by applying the first theorem to `star a` and then
using `rightSupport_star`.  It never asserts or uses `CFC.abs (star a) = CFC.abs a`, which would be
false in general.  Thus the two orientations remain valid for nonnormal elements.  No ready-made
finite-matrix `WStarAlgebra` instance was present in the narrow import graph for a concrete
nonnormal fixture; adding such a fixture or broad import solely for a test would not improve the
kernel-checked general proof.

## Dependency direction

The module has only the two public imports

```text
LeanOA.Mathlib.Analysis.CStarAlgebra.Abs
LeanOA.Ultraweak.Support
```

and therefore realizes the intended dependency chain

```text
general C-star absolute-value annihilators
        +
existing W-star one-sided supports
        ↓
source-facing absolute-value support identities.
```

`LeanOA.Ultraweak.Support` remains independent of CFC absolute value, and no production module
imports `Scratch`.

## Downstream WS-4 surface

WS-4 needs only the two declarations above.  After constructing a polar factor `u`, it can rewrite
the source initial- and final-projection targets through

```lean
WStarAlgebra.support_abs a
WStarAlgebra.support_abs_star a
```

to obtain the exact Sakai orientations

```text
star u * u = rightSupport a = support (CFC.abs a),
u * star u = leftSupport a = support (CFC.abs (star a)).
```

No additional zero-kernel corollary was published because WS-4 has no identified need beyond these
two rewrite endpoints; it can continue to use the established general kernel APIs directly.

## Validation and proof integrity

The focused build and module-specific Mathlib linter passed:

```text
lake build LeanOA.Ultraweak.AbsSupport
lake lint -- LeanOA.Ultraweak.AbsSupport
```

A signature and axiom audit using `lake env lean` confirmed both declarations at the stated
generality.  `#print axioms` reported exactly

```text
[propext, Classical.choice, Quot.sound]
```

for each theorem.  No custom axiom, `sorry`, `admit`, opaque mathematical placeholder, high
heartbeat setting, new support definition, or speculative corollary was added.
