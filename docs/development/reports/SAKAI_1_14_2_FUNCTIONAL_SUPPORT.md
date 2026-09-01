# Sakai 1.14.2: support of a normal positive functional

## Source

Source: Sakai, *$C^*$-Algebras and $W^*$-Algebras*, Definition 1.14.2,
printed p. 31 (local PDF p. 43). The source assumes a **normal positive linear functional**
`φ` on a $W^*$-algebra `M`. It does not assume that `φ` is nonzero, normalized, a state, or
faithful.

Sakai defines

```text
Lφ = {x ∈ M | φ(x* x) = 0}.
```

He states that `Lφ` is an `s(M,M*)`-closed left ideal, hence is
`σ(M,M*)`-closed by 1.8.11, and therefore has the form `M p₀` for a projection `p₀` by the
closed-left-ideal classification in 1.10.1. The projection `p₀` is the greatest projection `q`
such that `φ(q) = 0`. Sakai defines the support by

```text
s(φ) = 1 - p₀.
```

He then records, for every `x ∈ M`,

```text
φ(x) = φ(s(φ) x) = φ(x s(φ)) = φ(s(φ) x s(φ)).
```

Finally, Sakai **defines** `φ` to be faithful when `s(φ) = 1`. He separately defines a family
`{φᵢ}` of normal positive functionals to be faithful when simultaneous vanishing
`φᵢ(x* x) = 0` for every `i` implies `x = 0`.

The source does not print a separate assertion that the restriction of `φ` to
`s(φ) M s(φ)` is faithful. That support-corner result is a derived theorem. The distinction is
important for source fidelity: global faithfulness by full support is source text; corner
faithfulness is a reusable consequence.

The exact left/right orientation is fixed by `Lφ = M p₀`: `Lφ` is a left ideal generated on the
right. Consequently,

```text
x ∈ Lφ ↔ x * s(φ) = 0.
```

The formula with multiplication by `s(φ)` on the left would have the wrong orientation.

The separate source and architecture audit, including the direct PDF inspection and external
library comparison, is in `SAKAI_1_14_2_FUNCTIONAL_SUPPORT_SOURCE.md`.

## Null ideal

The general $C^*$-algebraic construction is:

```lean
def PositiveLinearMap.nullIdeal
    (φ : A →ₚ[ℂ] ℂ) : Ideal A
```

under

```lean
[CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
```

Its defining and coefficient characterizations, in the same context, are:

```lean
@[simp] lemma PositiveLinearMap.mem_nullIdeal
    (φ : A →ₚ[ℂ] ℂ) (x : A) :
    x ∈ φ.nullIdeal ↔ φ (star x * x) = 0

lemma PositiveLinearMap.mem_nullIdeal_iff_forall_apply_star_mul_eq_zero
    (φ : A →ₚ[ℂ] ℂ) (x : A) :
    x ∈ φ.nullIdeal ↔ ∀ y : A, φ (star y * x) = 0
```

The proof reuses `PositiveLinearMap.cauchy_schwarz_star_mul`. At the weaker common context

```lean
[NonUnitalRing A] [PartialOrder A] [Module ℂ A]
[StarRing A] [StarOrderedRing A] [SelfAdjointDecompose A]
[StarModule ℂ A] [IsScalarTower ℂ A A]
```

the two independently reusable zero-coefficient consequences are:

```lean
lemma PositiveLinearMap.apply_star_mul_eq_zero_of_apply_star_mul_self_eq_zero_left
    (f : A →ₚ[ℂ] ℂ) {x : A} (hx : f (star x * x) = 0) (y : A) :
    f (star x * y) = 0

lemma PositiveLinearMap.apply_star_mul_eq_zero_of_apply_star_mul_self_eq_zero_right
    (f : A →ₚ[ℂ] ℂ) {x : A} (hx : f (star x * x) = 0) (y : A) :
    f (star y * x) = 0
```

They are proved at the weaker abstract algebraic boundary already supporting the local GNS
semi-inner-product construction; they do not require a $W^*$-algebra or normality. The bundled
`Ideal A` construction is unital because that is Mathlib's canonical object for a left ideal and
because the source domain is unital. No local one-sided-ideal replacement was introduced.

The ideal laws follow from Cauchy--Schwarz coefficient vanishing:

- zero membership is immediate;
- both cross terms vanish in the expansion for `x + y`;
- if `x` is null, then `a * x` is null for every `a`, so the set is a left ideal.

Normality first appears only in the topological closedness theorems, not in `nullIdeal` itself.

## Closedness

The topology-specific declarations have the common context

```lean
[CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
[NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]
```

Their exact signatures are:

```lean
theorem PositiveLinearMap.IsNormalOnProjections.isClosed_nullIdeal_strong
    {φ : M →ₚ[ℂ] ℂ} (hφ : φ.IsNormalOnProjections) :
    IsClosed (Ultraweak.ofStrong ⁻¹' (φ.nullIdeal : Set M) : Set s(M, P))

theorem PositiveLinearMap.IsNormalOnProjections.isClosed_nullIdeal_ultraweak
    {φ : M →ₚ[ℂ] ℂ} (hφ : φ.IsNormalOnProjections) :
    IsClosed (Ultraweak.ofSubmodule (P := P)
      (φ.nullIdeal.restrictScalars ℂ) : Set σ(M, P))
```

The strong-closedness proof follows the source claim directly. Existing Section 1.13
infrastructure sends `hφ : φ.IsNormalOnProjections` to specified-predual continuous-dual
membership. The corresponding positive ultraweakly continuous functional `φu` supplies one of
the seminorms defining `s(M,P)`, and the proof identifies the null ideal with the zero set of

```text
Ultraweak.Strong.seminorm φu.
```

Continuity of that seminorm makes the set strongly closed.

The ultraweak-closedness proof follows Sakai's stated route rather than replacing it with a new
closure mechanism. It observes that the ideal is real-convex and applies

```text
Ultraweak.Strong.image_closure_toUltraweakEquiv
```

to use the equality of strong and ultraweak closures on convex sets. Thus both the intermediate
strong assertion and the cited strong-to-ultraweak passage are represented.

## Existing one-sided ideal infrastructure

The implementation reuses the existing classifier:

```text
Ideal.existsUnique_isStarProjection_eq_span_of_isClosed_ultraweak
```

It therefore does not rebuild Sakai 1.10.1 or introduce a second closed-ideal type. Existing
`Ideal.range_mulRight` records that `Ideal.span {p}` is the range `M p`, matching the source
orientation.

One small general ring lemma supplies the intrinsic annihilator bridge:

```lean
Ideal.mem_span_singleton_one_sub_iff_mul_eq_zero
    (hp : IsIdempotentElem p) :
    x ∈ Ideal.span {1 - p} ↔ x * p = 0
```

It is stated for a `Ring R` and an idempotent, with no star, topology, norm, order, or operator-
algebra assumptions. The `Ring` boundary is inherited from Mathlib's current unital `Ideal`
interface and the use of `1 - p`; the proof itself is elementary principal-ideal algebra. This is
the only new ideal helper needed by the support consumer.

The existing element-support API remains separate:

```text
WStarAlgebra.leftSupport
WStarAlgebra.rightSupport
WStarAlgebra.support
```

Those declarations concern algebra elements. Functional support belongs to
`PositiveLinearMap`, so no common wrapper or overloaded unqualified support object was added.

## Support definition

The single public functional-support definition is:

```lean
noncomputable def PositiveLinearMap.support
    (φ : M →ₚ[ℂ] ℂ) (hφ : φ.IsNormalOnProjections) :
    {p : M // IsStarProjection p}
```

under the ordinary intrinsic context

```lean
[CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] [WStarAlgebra M]
```

All intrinsic declarations in the remaining sections use this context unless a weaker context is
stated explicitly.

The explicit proof `hφ` is the weakest honest boundary for this construction. A nonnormal
positive functional need not have an ultraweakly closed null ideal, and Sak-AI has deliberately
not introduced a second bundled normal-functional type. Proof irrelevance prevents the proof
argument from carrying extra mathematical data.

The definition chooses `WStarAlgebra.predual M` only inside its implementation, applies the
unique closed-left-ideal generator theorem, and returns the complement of that generator. The
generator and its choice witness are not public definitions.

The source generator equation is exposed as:

```lean
theorem PositiveLinearMap.nullIdeal_eq_span_one_sub_support
    (φ : M →ₚ[ℂ] ℂ) (hφ : φ.IsNormalOnProjections) :
    φ.nullIdeal = Ideal.span {1 - (φ.support hφ).1}
```

There is no second `nullSupport` object, no functional-support structure, and no new normality
predicate.

## Greatest zero projection

The projection-level characterization is:

```lean
PositiveLinearMap.apply_eq_zero_iff_le_one_sub_support
    (φ : M →ₚ[ℂ] ℂ) (hφ : φ.IsNormalOnProjections)
    (q : {q : M // IsStarProjection q}) :
    φ q.1 = 0 ↔ q.1 ≤ 1 - (φ.support hφ).1
```

It is packaged in the exact order-theoretic form:

```lean
theorem PositiveLinearMap.isGreatest_setOf_apply_eq_zero
    (φ : M →ₚ[ℂ] ℂ) (hφ : φ.IsNormalOnProjections) :
    IsGreatest {q : {q : M // IsStarProjection q} | φ q.1 = 0}
      ⟨1 - (φ.support hφ).1, (φ.support hφ).2.one_sub⟩
```

This matches Sakai's `p₀`, not the support itself: the **complement** of support is the greatest
zero projection. The proof reduces a projection's quadratic value to its value, then uses the
existing projection identity `p * q = 0 ↔ p ≤ 1 - q`.

## Annihilator characterization

The stable abstraction boundary hiding the ideal generator is:

```lean
PositiveLinearMap.mem_nullIdeal_iff_mul_support_eq_zero
    (φ : M →ₚ[ℂ] ℂ) (hφ : φ.IsNormalOnProjections) (x : M) :
    x ∈ φ.nullIdeal ↔ x * (φ.support hφ).1 = 0
```

The direct quadratic form is:

```lean
PositiveLinearMap.apply_star_mul_self_eq_zero_iff_mul_support_eq_zero
    (φ : M →ₚ[ℂ] ℂ) (hφ : φ.IsNormalOnProjections) (x : M) :
    φ (star x * x) = 0 ↔ x * (φ.support hφ).1 = 0
```

These results preserve the right-multiplication orientation forced by `Lφ = M p₀`. Downstream
proofs can use the support directly and need not inspect the chosen ideal generator.

## Cutdown

The complement first gives two coefficient-vanishing lemmas:

```lean
theorem PositiveLinearMap.apply_mul_one_sub_support
    (φ : M →ₚ[ℂ] ℂ) (hφ : φ.IsNormalOnProjections) (x : M) :
    φ (x * (1 - (φ.support hφ).1)) = 0

theorem PositiveLinearMap.apply_one_sub_support_mul
    (φ : M →ₚ[ℂ] ℂ) (hφ : φ.IsNormalOnProjections) (x : M) :
    φ ((1 - (φ.support hφ).1) * x) = 0
```

They yield all three identities printed by Sakai:

```lean
@[simp] theorem PositiveLinearMap.apply_mul_support
    (φ : M →ₚ[ℂ] ℂ) (hφ : φ.IsNormalOnProjections) (x : M) :
    φ (x * (φ.support hφ).1) = φ x

@[simp] theorem PositiveLinearMap.apply_support_mul
    (φ : M →ₚ[ℂ] ℂ) (hφ : φ.IsNormalOnProjections) (x : M) :
    φ ((φ.support hφ).1 * x) = φ x

theorem PositiveLinearMap.apply_support_mul_support
    (φ : M →ₚ[ℂ] ℂ) (hφ : φ.IsNormalOnProjections) (x : M) :
    φ ((φ.support hφ).1 * x * (φ.support hφ).1) = φ x
```

The one-sided orientations are both public because Sakai records both and later functional polar
decomposition arguments use multiplication on a specified side. The two-sided theorem composes
the one-sided results. It is deliberately not an additional simp rule because the one-sided simp
lemmas already normalize its left-hand side. None of these theorems asserts that support is
central.

## Faithfulness

Sakai's full-support definition is connected to the usual quadratic-kernel formulation by:

```lean
PositiveLinearMap.support_eq_one_iff_apply_star_mul_self_eq_zero_imp
    (φ : M →ₚ[ℂ] ℂ) (hφ : φ.IsNormalOnProjections) :
    (φ.support hφ).1 = 1 ↔
      ∀ x : M, φ (star x * x) = 0 → x = 0
```

The left side uses the ambient value because the existing star-projection subtype has no `One`
instance. No `Faithful` predicate or wrapper was found in pinned Mathlib, audited current
Mathlib, original LeanOA, or the preexisting Sak-AI API, so this transaction remains theorem-level.

The derived support-corner theorem is:

```lean
PositiveLinearMap.apply_star_mul_self_eq_zero_iff_on_support_corner
    (φ : M →ₚ[ℂ] ℂ) (hφ : φ.IsNormalOnProjections)
    (x : (φ.support hφ).2.Corner) :
    φ (star (x : M) * (x : M)) = 0 ↔ x = 0
```

It reuses `IsStarProjection.Corner.mul_projection`: quadratic nullity gives
`x * s(φ) = 0`, while corner membership gives `x * s(φ) = x`.

The customary positive-element version is:

```lean
PositiveLinearMap.apply_eq_zero_iff_of_nonneg_on_support_corner
    (φ : M →ₚ[ℂ] ℂ) (hφ : φ.IsNormalOnProjections)
    (x : (φ.support hφ).2.Corner) (hx : 0 ≤ x) :
    φ (x : M) = 0 ↔ x = 0
```

Its proof uses `CFC.sqrt x` in the already established corner $C^*$-algebra and then applies the
star-square theorem. No new hereditary-corner or square-root infrastructure is needed.

These two corner declarations are explicitly **derived support API**, not verbatim sentences of
Definition 1.14.2. They are included because they express the mathematically standard meaning of
faithfulness on the support corner and have a concrete later consumer.

The source's faithful-family terminology remains unbundled in this transaction. Introducing a
predicate before a theorem consumes it would add a parallel abstraction without mathematical
payoff.

## Predual visibility

A specified predual `P` appears only in declarations whose conclusions explicitly mention
`s(M,P)` or `σ(M,P)`:

```text
PositiveLinearMap.IsNormalOnProjections.isClosed_nullIdeal_strong
PositiveLinearMap.IsNormalOnProjections.isClosed_nullIdeal_ultraweak
```

The definition `PositiveLinearMap.support`, its greatest-zero and annihilator
characterizations, the cutdown identities, and all faithfulness results require only the ordinary
`WStarAlgebra M` context. `WStarAlgebra.predual M` is selected inside the implementation and does
not escape through the public intrinsic API.

This matches the abstraction boundary used in Sections 1.12--1.13: selected preduals are visible
when a topology is named and hidden when the theorem is intrinsic to the $W^*$-algebra.

## Downstream use

This transaction supplies the support object and rewrite layer needed by the remainder of
Section 1.14.

- Theorem 1.14.3 uses supports and cutdown identities in the uniqueness argument for the
  orthogonal positive and negative parts of a self-adjoint predual functional.
- Theorem 1.14.4 uses `s(φ)` as the initial projection of the partial isometry in functional polar
  decomposition.
- In the uniqueness proof of 1.14.4, Sakai has `q = s(φ)`, an element `h ∈ qMq` with `h ≤ q`, and
  `φ(h) = φ(q)`, and concludes `h = q`. This is exactly the positive-element support-corner
  faithfulness mechanism: `q-h` is nonnegative in the corner and has zero functional value.

The next bounded source transaction is:

```text
Definition 1.14.1 (orthogonality of positive functionals)
  + Theorem 1.14.3 (orthogonal Jordan decomposition of a self-adjoint predual functional).
```

Definition 1.14.1 should be introduced only in the form actually consumed by Theorem 1.14.3.
The existing self-adjoint functional factorization in `Ultraweak.PolarDecomposition`, together
with the support/cutdown API above, should be audited before reproducing Sakai's existence proof.
Theorem 1.14.4 remains the subsequent target after the orthogonal decomposition is stable.

## Reuse and generality summary

The implementation reuses Mathlib's `Ideal`, positive linear maps, star projections, continuous
functional calculus, and Scott-continuity vocabulary; original LeanOA's positive-functional
Cauchy--Schwarz argument; and Sak-AI's specified preduals, intrinsic strong topology, closure
bridge, closed-left-ideal classifier, projection order, element support, and corner APIs.

Pinned and audited current Mathlib, original LeanOA, and preexisting Sak-AI contain no functional-
support or positive-functional faithfulness API that subsumes these declarations. The new
surface therefore consists of one source definition and theorem families around canonical
existing objects, rather than a competing foundation.

Generality was checked declaration by declaration:

- coefficient-zero lemmas remain below the $C^*$ boundary supported by the existing GNS argument;
- `nullIdeal` is $C^*$-algebraic and does not assume normality;
- the complement-of-idempotent ideal lemma is purely ring-theoretic;
- only topology-naming theorems expose a specified predual;
- support and its intrinsic consequences require exactly normality plus the ordinary
  $W^*$-algebra context;
- corner faithfulness reuses the existing corner rather than defining a restriction object;
- no theorem assumes nonzeroness, state normalization, factor structure, separability, or
  countability.
