# Polar-decomposition $C^*$-algebra API report

Date: 2026-08-31

Workstream: WS-1, Sakai Section 1.12

Baseline: `f840ec2643a255cf1fcbb5c69da316c74417829f`

## Scope and outcome

This workstream adds only the general algebra needed before the $W^*$-algebra support and
compactness layers of Sakai's element polar decomposition. Mathlib's `CFC.abs` remains the unique
absolute-value construction. No partial-isometry predicate, support projection, polar factor,
topology, PVM, or spectral integral was introduced.

The production surface consists of exact one-sided annihilator equivalences for `CFC.abs` and the
minimal fixing/projection consequences of assuming that `star u * u` is a star projection.

## Overlap audit

The audit searched by declaration name and mathematical content in:

- Sak-AI at baseline `f840ec2643a255cf1fcbb5c69da316c74417829f`;
- pinned Mathlib at `476ab284693e554a6b48c5f5210cb4fb5ae51252`;
- the available current-Mathlib checkout at
  `567908cf509fb0bab796e5401edf35b4492ae48f`;
- the read-only original LeanOA checkout at
  `cb811c1006ae78a0ff1d175253200e1859843370`.

The following existing results are reused rather than reproved:

- `CFC.abs_mul_abs` identifies `CFC.abs a * CFC.abs a` with `star a * a`;
- `CFC.abs_nonneg` supplies self-adjointness of `CFC.abs a`;
- `CStarRing.star_mul_self_eq_zero_iff` detects zero elements in a nonunital $C^*$-algebra;
- Sak-AI's existing `IsSelfAdjoint.mul_eq_self_of_star_mul_self_mul_eq` turns a self-adjoint
  right identity for `star u * u` into a right identity for `u`;
- pinned Mathlib's
  `isIdempotentElem_star_mul_self_iff_isIdempotentElem_self_mul_star` transfers idempotence from
  `star u * u` to `u * star u`.

In particular, the final-projection proof uses Mathlib's exact idempotence-transfer theorem; it
does not reprove that result from the fixing identity.

Neither pinned/current Mathlib nor Sak-AI contains the two one-sided `CFC.abs` annihilator
equivalences below. Original LeanOA contains extreme-point-specific theorems showing that both
products are projections, but no corresponding theorem under an arbitrary
`IsStarProjection (star u * u)` hypothesis and no absolute-value annihilator API. No general
element polar-decomposition or partial-isometry object was found in these audited trees.

## Added declarations

### Absolute-value annihilators

The new module `LeanOA.Mathlib.Analysis.CStarAlgebra.Abs` exposes:

```lean
CFC.abs_mul_eq_zero_iff (a x : A) :
  CFC.abs a * x = 0 ↔ a * x = 0

CFC.mul_abs_eq_zero_iff (x a : A) :
  x * CFC.abs a = 0 ↔ x * star a = 0
```

Both results assume

```lean
[NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
```

which is the standard nonunital $C^*$-algebra interface under which Mathlib's ordered
self-adjoint CFC absolute value elaborates. They require neither a unit nor $W^*$-algebra or
support infrastructure, and `x` is arbitrary rather than a projection.

The second orientation is intentionally about `star a`. For nonnormal `a`, replacing it with
`a` would be an incorrect statement. Its proof is obtained from the first equivalence by taking
stars, without using or asserting `CFC.abs (star a) = CFC.abs a`.

### Partial-isometry consequences

The existing module `LeanOA.Mathlib.Analysis.CStarAlgebra.Projection` now exposes:

```lean
IsStarProjection.mul_star_mul_self
    (hu : IsStarProjection (star u * u)) :
    u * star u * u = u

IsStarProjection.mul_star_mul_self_assoc
    (hu : IsStarProjection (star u * u)) :
    u * (star u * u) = u

IsStarProjection.mul_star_self
    (hu : IsStarProjection (star u * u)) :
    IsStarProjection (u * star u)
```

These declarations require only `[NonUnitalCStarAlgebra A]`. The first is the canonical
left-associated partial-isometry identity; the second gives the exact right-associated rewrite
needed when `star u * u` is treated as the initial projection. Thus both orientations named in the
Section 1.12 contract are directly available. The third packages the corresponding final
projection, reusing Mathlib's idempotence transfer and the automatic self-adjointness of
`u * star u`.

The concrete CFC imports used only to prove `IsStarProjection.mul_star_self` are private imports of
the projection extension module, so this small API does not re-export a new CFC layer.

## CFC compatibility and dependency direction

`LeanOA.Mathlib.Analysis.CStarAlgebra.Abs` imports Mathlib's canonical absolute-value module and
adds theorem-level bridges only. The dependency direction is

```text
Mathlib CFC.abs and C-star zero detection
        ↓
general C-star annihilator equivalences
        ↓
future W-star support bridge
```

No support fact appears in the C-star module. This keeps WS-2 free to translate annihilation into
the existing `WStarAlgebra.leftSupport` and `rightSupport` universal properties without importing
support infrastructure back into the general layer.

## Downstream signatures

WS-2 may use `CFC.abs_mul_eq_zero_iff` with an arbitrary right multiplier, in particular a support
complement, to transfer right annihilation from `a` to `CFC.abs a`. It may use
`CFC.mul_abs_eq_zero_iff` for the star-symmetric left-annihilator statement. These signatures are
stable and contain no proof-local regularizer object.

WS-4 may use `hu.mul_star_mul_self_assoc` to rewrite multiplication by the initial projection and
`hu.mul_star_self` to obtain the final star projection once the cluster point's initial product is
identified.

## Upstream assessment

The two `CFC.abs` annihilator equivalences are plausible Mathlib candidates: they use only the
canonical CFC absolute value and standard nonunital $C^*$-algebra structure, and arbitrary
multipliers make them reusable beyond polar decomposition. The projection implication and fixing
identity are also small upstream candidates. The explicitly right-associated fixing corollary is
primarily an ergonomic rewrite and can be reviewed together with the canonical identity if an
upstream proposal is prepared.

## Validation and proof integrity

The following focused checks passed:

```text
lake build LeanOA.Mathlib.Analysis.CStarAlgebra.Abs
lake build LeanOA.Mathlib.Analysis.CStarAlgebra.Projection
lake build LeanOA.Mathlib.Analysis.CStarAlgebra.Projection \
  LeanOA.Mathlib.Analysis.CStarAlgebra.Abs
```

A downstream signature test checked both requested association forms, the final-projection result,
and both annihilator equivalences. `#print axioms` reported exactly

```text
[propext, Classical.choice, Quot.sound]
```

for each of:

- `IsStarProjection.mul_star_mul_self`;
- `IsStarProjection.mul_star_mul_self_assoc`;
- `IsStarProjection.mul_star_self`;
- `CFC.abs_mul_eq_zero_iff`;
- `CFC.mul_abs_eq_zero_iff`.

No custom axiom, `sorry`, `admit`, opaque mathematical placeholder, or new high-heartbeat setting
was added.
