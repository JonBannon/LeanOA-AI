# The vector-coefficient test space of `B(H)`

## Status and source connection

This transaction formalizes the finite vector-coefficient layer used at the beginning of Sakai
§1.15. It does **not** construct the norm-completed predual of `B(H)`, identify the concrete
σ-WOT with a predual weak topology, or prove Proposition 1.15.1.

**Supersession note (2026-09-02):** those limitations describe this historical transaction.
Subsequent modules construct the concrete predual and one-sided comparison APIs, and
`NonUnitalStarSubalgebra.operatorTopologyClosedness_tfae` now source-formalizes Proposition
1.15.1 without asserting equality of the topologies.

In the inspected 1971 edition, Sakai defines WOT on printed page 34 (PDF page 46) by the
seminorms

\[
  T \longmapsto |(T\xi,\eta)|.
\]

His scalar product is linear in the first variable; in particular, `(Tξ,η)` is a complex-linear
functional of `T`. Mathlib's inner product is linear in the second variable. The source
coefficient is therefore represented in Lean as `⟪η, T ξ⟫_𝕜`.

On the same page Sakai lets `V` be the linear space of all WOT-continuous linear functionals and
states that WOT is `σ(B(H),V)`. His σ-WOT is generated separately by

\[
  T \longmapsto \left|\sum_n (T\xi_n,\eta_n)\right|
\]

for two square-summable vector sequences. The present finite-span API is designed to be the dense
algebraic input to that later completion, but no infinite series or completion is defined here.

## Coefficient functional

The generic definition is

```lean
ContinuousLinearMap.vectorFunctional (ξ : E) (η : F) :
    (E →L[𝕜] F) →L[𝕜] 𝕜
```

and its application theorem is

```lean
ContinuousLinearMap.vectorFunctional_apply :
  vectorFunctional ξ η T = ⟪η, T ξ⟫_𝕜
```

The construction is the composition of Mathlib's existing APIs

```lean
ContinuousLinearMap.apply 𝕜 F ξ
innerSL 𝕜 η
```

No bundled vector functional with this role was found in pinned Mathlib, so only the missing
composition and its reusable interface were added.

## Generality

The base definition, raw family, span, and separation API work over any `RCLike 𝕜`, for a
seminormed `𝕜`-space `E` and an inner-product space `F`. Completeness and an inner product on the
domain are added only by the adjoint results that require them. The WOT identification assumes
that `F` is complete, exactly as Mathlib's Hilbert-space coefficient characterization of WOT does.

The source specialization is `𝕜 = ℂ` and `E = F = H`. No declaration assumes `Nontrivial H`.

## Separation

The raw coefficients and their span both separate operators:

```lean
ContinuousLinearMap.ext_vectorFunctional
ContinuousLinearMap.eq_zero_of_forall_vectorFunctional_eq_zero
ContinuousLinearMap.ext_vectorFunctionalSpan
ContinuousLinearMap.eq_zero_of_forall_mem_vectorFunctionalSpan_eq_zero
```

The zero theorem substitutes `η := T ξ` and applies `inner_self_eq_zero`; it does not choose a
nonzero vector. It therefore also covers the zero/subsingleton Hilbert space.

## Star stability

For adjoints and endomorphism star, the exact formulas are

```lean
ContinuousLinearMap.vectorFunctional_adjoint_apply :
  vectorFunctional η ξ (T†) = star (vectorFunctional ξ η T)

ContinuousLinearMap.vectorFunctional_star_apply :
  vectorFunctional ξ η (star T) = star (vectorFunctional η ξ T)
```

Mathlib already defines the intrinsic involution on continuous linear maps as a `WithConv`
construction. Reusing that operation, Sak-AI proves both the generator formula and actual
span-level stability:

```lean
ContinuousLinearMap.intrinsicStar_vectorFunctional
ContinuousLinearMap.intrinsicStar_mem_vectorFunctionalSpan
```

Thus star stability is kernel-proved and is not merely an assertion in this report.

## Left and right invariance

For `B(H)`, fixed multiplication transforms generators by

```lean
ContinuousLinearMap.vectorFunctional_mul_left :
  vectorFunctional ξ η (a * T) = vectorFunctional ξ (star a η) T

ContinuousLinearMap.vectorFunctional_mul_right :
  vectorFunctional ξ η (T * a) = vectorFunctional (a ξ) η T
```

The more general composition versions are `vectorFunctional_comp_left` and
`vectorFunctional_comp_right`. The span is proved stable under right multiplication without a
completeness assumption, and under left or two-sided multiplication when the adjoint is
available:

```lean
ContinuousLinearMap.comp_mulRight_mem_vectorFunctionalSpan
ContinuousLinearMap.comp_mulLeft_mem_vectorFunctionalSpan
ContinuousLinearMap.comp_mulLeftRight_mem_vectorFunctionalSpan
```

The two-sided generator formula is

```lean
ContinuousLinearMap.vectorFunctional_comp_mulLeftRight
```

and sends `ω_{ξ,η} ∘ (T ↦ aTb)` to `ω_{bξ,a*η}`.

## Linear span

The raw family and its algebraic span in the operator-norm dual are

```lean
ContinuousLinearMap.vectorFunctionals
ContinuousLinearMap.vectorFunctionalSpan
```

Generator membership is available through
`ContinuousLinearMap.vectorFunctional_mem_span`. This is an algebraic span, not its closure for
any proposed predual norm.

## WOT identification

Evaluation against the span is bundled as

```lean
ContinuousLinearMap.vectorFunctionalPairing :
  (E →L[𝕜] F) →ₗ[𝕜] vectorFunctionalSpan →ₗ[𝕜] 𝕜
```

No new WOT type is defined. The two continuous identity maps are

```lean
ContinuousLinearMapWOT.fromVectorFunctionalWeak
ContinuousLinearMapWOT.toVectorFunctionalWeak
```

and the bidirectional identification is

```lean
ContinuousLinearMapWOT.vectorFunctionalWeakEquiv :
  WeakBilin ContinuousLinearMap.vectorFunctionalPairing ≃L[𝕜] (E →WOT[𝕜] F)
```

The forward direction uses each raw coefficient as an element of the span and Mathlib's WOT
coefficient characterization. The reverse direction is span induction: WOT-continuity of raw
coefficients is closed under zero, addition, and scalar multiplication. This proves rather than
assumes that passing from the raw family to its linear span does not change the induced topology.

On Mathlib's actual WOT carrier, the pairing

```lean
ContinuousLinearMapWOT.vectorFunctionalPairing
```

has the instance

```lean
ContinuousLinearMapWOT.vectorFunctionalPairing_isWeak :
  ContinuousLinearMapWOT.vectorFunctionalPairing.IsWeak
```

This is the exact Lean certificate of

\[
  \sigma(E \toL F,V)=\operatorname{WOT},
\]

and in particular of `σ(B(H),V) = Mathlib WOT`.

Both sides of the pairing separate. The weak representation theorem then gives

```lean
ContinuousLinearMapWOT.vectorFunctionalSpanEquivDual :
  vectorFunctionalSpan ≃ₗ[𝕜] StrongDual 𝕜 (E →WOT[𝕜] F)
```

so the formal finite span is exactly the space of all WOT-continuous linear functionals in
Sakai's definition of `V`. This is a linear/topological-dual statement, not a claim that `V` is
complete in the inherited operator-dual norm.

## `WeakTestSpace` integration

The new construction deliberately uses the same `WeakBilin` and `LinearMap.IsWeak` semantic core
as Sak-AI's existing test-space machinery. It does not add a competing test-space structure.

A literal term of type `Ultraweak.WeakTestSpace V` cannot yet be constructed honestly. That type
expects `V : Submodule ℂ P` for an already chosen complete `P` equipped with
`[Predual ℂ M P]`; moreover, it puts the weak topology induced by `M` on the functional coordinate
`V`. The present construction supplies the complementary topology `σ(M,V)` before such a `P`
exists. Pretending that the algebraic span itself were the completed predual would assume the
principal missing theorem.

After the completion `P_H` is built, the required integration bridge is precise:

1. embed `vectorFunctionalSpan` into `P_H`;
2. prove that the restricted `Ultraweak.testPairing` agrees with
   `ContinuousLinearMap.vectorFunctionalPairing`;
3. transfer the proved star and multiplier invariance;
4. prove norm density by the definition/completion theorem;
5. construct `Ultraweak.SakaiInvariantTestSpace` and hence use `WeakTestSpace` and
   `SakaiMackey`.

## Downstream consequences and limits

Available now:

- canonical WOT as `σ(B(H),V)` with both topology directions;
- separation and the exact WOT continuous dual;
- star and fixed-multiplier stability of the finite test space;
- all generic `LinearMap.IsWeak` consequences for the concrete WOT pairing;
- a stable algebraic input for the concrete-predual completion.

Not available merely from this transaction:

- a Banach predual instance for `B(H)`;
- a `SakaiInvariantTestSpace` instance inside that predual;
- σ-WOT = `σ(B(H),B(H)_*)`;
- ultrastrong = intrinsic strong topology;
- relative Kaplansky density inside a WOT closure;
- Sakai Proposition 1.15.1.

The source status remains:

```text
Sakai Proposition 1.15.1: NOT SOURCE-FORMALIZED
```
