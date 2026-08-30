# Fixed-projection ultraweak infrastructure audit

Date: 2026-08-30

Workstream baseline: `73ef4aff6299383a8be773168d64611f2a575315`, whose parent is the
integrated truncated-affine baseline `162271ac17505779d1b2345ef5d4de434bf82c49`.

## Scope and conclusion

The fixed left, right, and two-sided multiplication steps needed in Sakai's competing-resolution
argument already follow from the established specified-ultraweak API.  Passing order inequalities
to the limit likewise follows from Sak-AI's `OrderClosedTopology` instance and Mathlib's generic
order-topology lemmas.  No new spectral-specific topology theorem and no norm substitute is needed.

The only production API addition proposed by this workstream is
`WStarAlgebra.support_le_iff`.  It is the missing semantic bridge saying that the support of a
self-adjoint element is the least projection acting as a left identity.  The theorem is a direct
specialization of the existing `leftSupport_le_iff`, has its natural home in
`LeanOA.Ultraweak.Support`, and lets clients avoid unfolding `support`.  The existing
`spectralProjectionIio_le_iff` is refactored to consume this bridge.

All other wrapper statements were kernel-checked in the isolated worker file
`Scratch/FixedProjectionUltraweak.lean` at worker commit `c637cb7` and deliberately remain
scratch-only; that file is not part of the integrated theorem tree.

## Sources audited

| Source | Revision | Result |
| --- | --- | --- |
| Sak-AI | `73ef4aff` | Complete fixed-multiplication and order-limit infrastructure; one missing support bridge |
| Pinned Mathlib | `476ab284693e554a6b48c5f5210cb4fb5ae51252` | Generic separate-multiplication and order-closed limit lemmas already present |
| Current Mathlib | `3c8e222f6536ac9643441d449c4f9c872336c095` | Relevant theorem signatures unchanged; changes in the inspected files are attributes/cosmetic cleanup |
| Original LeanOA | `cb811c1006ae78a0ff1d175253200e1859843370` | Has the predecessor `OrderClosedTopology` proof, but no general ultraweak multiplication module or support API |

The current-Mathlib comparison used a read-only shallow sparse clone in `/private/tmp`; the pinned
dependency and original LeanOA checkout were not modified.

## Existing fixed-multiplication API

For a $C^*$-algebra `M` with specified complete predual `P`, Sak-AI already supplies:

- `Ultraweak.continuous_mulLeftₗ`;
- `Ultraweak.continuous_mulRightₗ`;
- `Ultraweak.mulLeftL` and `Ultraweak.mulRightL` as continuous linear maps;
- `SeparatelyContinuousMul σ(M, P)` and `IsSemitopologicalRing σ(M, P)` instances;
- `Ultraweak.toUltraweak_mul` and `Ultraweak.ofUltraweak_mul` as explicit transport bridges.

Consequently, if `h : Tendsto f l (nhds x)` in `σ(M,P)`, Mathlib gives directly:

```lean
h.const_mul p
h.mul_const p
(h.const_mul p).mul_const q
```

These are respectively the fixed-left, fixed-right, and fixed-two-sided limit statements.  The
last statement uses only separate continuity: no unsupported joint ultraweak continuity is being
asserted.

For an `M`-valued net whose convergence is stated after `toUltraweak`, the scratch file verifies
that `simpa only [Ultraweak.toUltraweak_mul]` transports these same generic results.  A dedicated
public wrapper would duplicate the existing interface without removing a real proof burden.

## Congruence

Mathlib's `Filter.Tendsto.congr'` transports a limit across eventual equality.  The scratch theorem
`tendsto_toUltraweak_congr'` confirms that an eventual equality in `M` is converted pointwise with
`congr_arg (toUltraweak ℂ P)`.  No Sak-AI-specific congruence theorem is missing.

When two ultraweak limits are compared by uniqueness, the filter must be nontrivial and the target
Hausdorff; the ordinary spectral nets meet these requirements.  Eventual-equality transport itself
does not need a `NeBot` hypothesis.

## Positive cone, order intervals, and inequalities at limits

`LeanOA.Ultraweak.OrderClosed` proves:

```lean
Ultraweak.isClosed_nonneg : IsClosed {x : σ(M,P) | 0 ≤ x}
instance : OrderClosedTopology σ(M,P)
```

The instance immediately exposes Mathlib's general:

- `isClosed_Ici`, `isClosed_Iic`, and `isClosed_Icc`;
- `le_of_tendsto_of_tendsto` (alias `tendsto_le_of_eventuallyLE`);
- `le_of_tendsto_of_tendsto'` for pointwise inequalities;
- `le_of_tendsto_of_tendsto_of_frequently` when frequency, rather than an eventual statement and
  a `NeBot` instance, is the natural input.

The scratch theorem `le_of_tendsto_toUltraweak` kernel-checks the exact transported formulation:
if `f → x`, `g → y` specified-ultraweakly and eventually `f i ≤ g i`, then `x ≤ y`.
Its constant-left, constant-right, and nonnegative corollaries also compile.  The `NeBot l`
hypothesis is mathematically necessary for the eventual-inequality formulation and must not be
silently omitted.

Thus a finite inequality such as `c • p ≤ xᵢ` passes to `c • p ≤ x` by applying
`le_of_tendsto_of_tendsto` to the constant net and the approximating net.  There is no missing
ultraweak closedness theorem here.

## Projection and support implications

Projection multiplication identities already come from Mathlib's:

```lean
IsStarProjection.le_iff_mul_eq_left
IsStarProjection.le_iff_mul_eq_right
```

Sak-AI already has `leftSupport_le_iff`, `rightSupport_le_iff`, `support_mul`, `mul_support`,
`leftSupport_mono_of_nonneg`, and nonzero-scalar invariance of left and right support.

The new proposed bridge is:

```lean
WStarAlgebra.support_le_iff (x : selfAdjoint M)
    (p : {p : M // IsStarProjection p}) :
  support x ≤ p ↔ p.1 * x.1 = x.1
```

It supplies the first support implication required by the source proof: after fixed-left
multiplication is passed through the ultraweak limit and gives `p * x = x`, the bridge gives
`support x ≤ p`.

For the reverse implication, the scratch file also kernel-checks:

1. `leftSupport p = p` for a star projection `p`;
2. if `0 < c` and `c • p ≤ x` for self-adjoint `x`, then `p ≤ support x`.

The second result is a short composition of projection support, nonzero real-scalar invariance,
and `leftSupport_mono_of_nonneg`.  It remains scratch-only in this stream because the support
recovery workstream should determine whether the exact coefficient and hypothesis shape is the
stable consumer-facing theorem.

## Exact use in the competing-resolution proof

Suppose finite approximants `S i` converge specified-ultraweakly to `x`.

- If every `S i` satisfies `p * S i = S i`, then fixed-left continuity gives
  `p * S i → p * x`; congruence gives `p * S i → x`; uniqueness of limits yields
  `p * x = x`, hence `support x ≤ p`.
- If every `S i` satisfies `c • q ≤ S i`, order-closedness passes the inequality to
  `c • q ≤ x`; for `c > 0`, the checked support argument yields `q ≤ support x`.
- If a compressed expression is needed, fixed-left followed by fixed-right continuity gives
  `p * S i * p → p * x * p`.

The outstanding work is therefore not fixed-multiplication or order topology.  It is the
source-faithful finite partition decomposition that produces the two displayed identities under
Sakai's actual ultraweak representation hypotheses.

## Mathlib overlap and upstream assessment

Pinned and current Mathlib already contain the optimal general topology statements.  Adding
ultraweak-named copies would be harmful duplication.  Current Mathlib differs from the pinned
revision in the inspected files only through unrelated cleanup and `closedness` attributes; it does
not add a specified-predual or $W^*$-support layer replacing Sak-AI's results.

`WStarAlgebra.support_le_iff` is not presently a Mathlib-upstream candidate because Mathlib has no
corresponding general $W^*$-support object in the audited tree.  If that object is upstreamed later,
the theorem should accompany it.  This audit identifies no new entry that must be added to
`MATHLIB_GAPS.md`.

## Validation

The following passed in the isolated worktree:

```text
lake build LeanOA.Ultraweak.Support
  3066 jobs

lake build LeanOA.Ultraweak.Support LeanOA.Ultraweak.SpectralProjection
  3068 jobs

lake env lean Scratch/FixedProjectionUltraweak.lean
  no errors or warnings

lake build
  3113 jobs

lake lint
  passed for LeanOA
```

No `sorry`, `admit`, new axiom, topology instance, spectral structure, or norm replacement was
introduced.
