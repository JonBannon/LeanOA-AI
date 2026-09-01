# Sakai 1.14.1 and 1.14.3: orthogonality and Jordan-decomposition source audit

## Status and scope

This is the WS-14D source and existing-factorization audit for Sakai, Definition 1.14.1 and
Theorem 1.14.3. It reconstructs the printed source, compares it with the existing Sak-AI and
external APIs, and recommends the shortest faithful implementation route. It does not itself
mark either item source-formalized; completion status belongs in the corresponding Verso blocks
after production Lean is integrated.

Baseline audited:

```text
Sak-AI                  ffb61d2e1abd8d5a66076762a43d0e2a90beafce
pinned Mathlib          476ab284693e554a6b48c5f5210cb4fb5ae51252
audited current Mathlib 567908cf509fb0bab796e5401edf35b4492ae48f
original LeanOA         cb811c1006ae78a0ff1d175253200e1859843370
```

The governing reuse requirement for this work is:

> Before introducing any new foundational theorem or proof pattern, search Mathlib, search the original LeanOA repository, and search the current Sak-AI repository for an existing theorem, definition, abstraction, or argument that already supplies the needed mathematics; reuse it where mathematically faithful, preserve architectural continuity with the APIs already built, and generalize only when that genuinely improves portability or reuse rather than duplicating local infrastructure.

## Direct source reconstruction

Source: Sakai, *$C^*$-Algebras and $W^*$-Algebras*, Section 1.14, printed pp. 31--32
(local `SakaiBook_1971.pdf`, PDF pp. 43--44). The pages were inspected directly from the scan;
the statements below are not inferred from a secondary summary.

### Definition 1.14.1

For two positive linear functionals `φ₁` and `φ₂` on a $C^*$-algebra `A`, Sakai says that
`φ₁` is orthogonal to `φ₂` precisely when

```text
‖φ₁ - φ₂‖ = ‖φ₁‖ + ‖φ₂‖.
```

The source definition is therefore:

- norm-theoretic;
- symmetric, although it is phrased directionally as “`φ₁` is orthogonal to `φ₂`”;
- defined for arbitrary positive functionals on a $C^*$-algebra;
- independent of normality, a predual, support projections, and $W^*$-structure.

It is **not** printed as any of the following:

```text
‖φ₁ - φ₂‖ = ‖φ₁ + φ₂‖
s(φ₁) s(φ₂) = 0
Disjoint (s(φ₁)) (s(φ₂)).
```

For positive functionals the first alternative is mathematically equivalent because the norm of
a positive functional is its value at `1`, but replacing the printed equality by that alternative
would still be a source translation, not the definition. Support orthogonality is a structural
characterization available only after normality and the $W^*$ support API are present; it must not
replace Definition 1.14.1.

### Theorem 1.14.3

The exact source assumptions are:

1. `M` is a $W^*$-algebra;
2. `M_*` is its predual;
3. `f ∈ M_*`;
4. `f* = f`.

The exact conclusion is that there are normal positive linear functionals `f₁` and `f₂` such that

```text
f = f₁ - f₂
‖f‖ = ‖f₁‖ + ‖f₂‖,
```

and that such a decomposition is unique. Sakai calls this the **orthogonal decomposition** of
`f` and writes

```text
f₁ = f⁺
f₂ = f⁻.
```

The theorem does not put support orthogonality in its displayed statement. By Definition 1.14.1,
the displayed norm identity says exactly that the two positive parts are orthogonal. The source
does name the parts `f⁺` and `f⁻`, but this notation alone does not force Sak-AI to introduce
choice-based public definitions before a downstream theorem needs them.

There are no factor, separability, sigma-finiteness, nonzero, state, or normalization assumptions.
The printed proof normalizes to `‖f‖ = 1`. A literal formalization of that normalization would
separate the zero case; the accepted production route instead delegates all cases to the existing
self-adjoint functional factorization.

### Source proof: existence

The printed proof proceeds as follows.

1. Normalize to `‖f‖ = 1`.
2. Use ultraweak compactness of the self-adjoint unit ball to find a norm-one self-adjoint element
   on which `f` takes the value `1`.
3. Take an extreme point `u` of the exposed face on which `f = 1`. By Sakai 1.6.4, `u` is a
   self-adjoint unitary.
4. Write

   ```text
   u = p - p',    p' = 1 - p,
   ```

   for complementary projections `p` and `p'`.
5. Define

   ```text
   f₁(x) = f(p x)
   f₂(x) = -f(p' x).
   ```

6. First prove `f₁ + f₂ ≥ 0` from

   ```text
   (f₁ + f₂)(1) = 1 = ‖f₁ + f₂‖,
   ```

   using the positive-functional criterion cited as 1.5.2.
7. Prove that `f₁` is positive on `p M p`. The contradiction argument uses the norm-attaining
   element `u = p - p'`. The identity

   ```text
   f₁ = (f + f₁ + f₂) / 2
   ```

   then makes `f₁` self-adjoint; this gives `f₁(p y p) = f₁(y)` and promotes positivity from the
   corner to all of `M`. The same argument applies to `f₂`.
8. Ultraweak continuity of the parts follows from ultraweak continuity of `f` and separate
   ultraweak continuity of fixed multiplication. Thus the parts are normal.
9. Evaluation on `p - p'` gives

   ```text
   ‖f₁ - f₂‖ = ‖f₁‖ + ‖f₂‖.
   ```

This proof does **not** invoke Sakai's functional polar-decomposition theorem: Theorem 1.14.4 is
the next theorem. Its extreme-point/self-adjoint-unitary core is, however, already encapsulated by
Sak-AI's existing functional factorization theorem described below.

### Source proof: uniqueness and use of 1.14.2

Suppose

```text
f = f₁ - f₂ = f₁' - f₂'
```

with all four functionals positive and with the required norm-additive decompositions. Since the
norm of a positive functional is its value at `1`, equality of the sums and evaluation of the two
differences at `1` give

```text
‖fᵢ‖ = ‖fᵢ'‖    (i = 1, 2).
```

The constructed first support satisfies `s(f₁) ≤ p`. Evaluating the competing decomposition on
`s(f₁)` yields

```text
f(s(f₁)) = f₁(s(f₁)) = ‖f₁‖
          = ‖f₁'‖ = f₁'(s(f₁)) - f₂'(s(f₁)).
```

Positivity forces `f₂'(s(f₁)) = 0` and `f₁'(s(f₁)) = ‖f₁'‖`. The greatest-zero-projection and
support-cutdown results of Definition 1.14.2 then give the relevant support comparisons, in
particular `s(f₁') ≤ s(f₁)`, and allow the calculation

```text
f₁(x) = f(s(f₁) x) = f₁'(s(f₁) x) = f₁'(x).
```

Hence `f₁ = f₁'`, and the difference equation gives `f₂ = f₂'`.

Thus 1.14.2 is used explicitly in the uniqueness half, through greatest-zero/support comparison
and cutdown. Existence is independent of functional support.

## Existing `Ultraweak.PolarDecomposition` audit

The existing public theorem is:

```lean
theorem Ultraweak.exists_positive_comp_mulLeft_of_isSelfAdjoint
    {M P : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
    [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]
    (f : σ(M, P) →L[ℂ] ℂ) (hf : IsSelfAdjoint (WithConv.toConv f)) :
    ∃ (u : M) (phi : σ(M, P) →P[ℂ] ℂ), IsSelfAdjoint u ∧ u ∈ unitary M ∧
      f = phi.toContinuousLinearMap.comp (Ultraweak.mulLeftL (P := P) u)
```

The unqualified `mulLeftL` in the source file is in namespace `Ultraweak`; its application law is

```lean
Ultraweak.mulLeftL_apply (a : M) (x : σ(M, P)) :
  Ultraweak.mulLeftL (P := P) a x =
    Ultraweak.toUltraweak ℂ P (a * Ultraweak.ofUltraweak x).
```

Consequently the factorization says, on underlying algebra elements,

```text
f(x) = phi(u x).
```

### What is already present

- The input is an arbitrary self-adjoint ultraweakly continuous functional, exactly the class
  needed by 1.14.3.
- The self-adjoint condition is the canonical existing intrinsic-star condition on a continuous
  linear functional.
- The theorem produces a positive ultraweakly continuous functional.
- It produces a self-adjoint **unitary**, stronger than the partial isometry used for a general
  functional in 1.14.4.
- Its proof already performs the compact exposed-face/extreme-point argument underlying Sakai's
  existence proof.
- The public theorem handles the subsingleton algebra separately; the nontrivial-algebra engine is
  private.

Pulling `phi` back to `M` uses the existing positive map

```lean
(phi.comp (Ultraweak.toUltraweakPosCLM P)).toPositiveLinearMap : M →ₚ[ℂ] ℂ.
```

Its normality follows through the already used bridge

```lean
PositiveLinearMap.isNormalOnProjections_of_mem_continuousDual
```

or equivalently

```lean
PositiveLinearMap.isNormalOnProjections_iff_mem_continuousDual.
```

This conversion pattern is already present in `Ultraweak.PredualUniqueness`; it should be reused
rather than recreated as a new normal-functional type.

### What is not present

The theorem does not presently expose:

- the complementary projections associated with `u`;
- positive and negative functionals;
- a difference decomposition;
- norm equality between `f` and `phi`;
- norm additivity of positive and negative parts;
- functional supports or their orthogonality;
- uniqueness;
- an exact `ExistsUnique` package for 1.14.3.

It is therefore not already Theorem 1.14.3, but it contains the difficult analytic existence
engine. It should be refined by small downstream bridges, not replaced by a second decomposition
argument.

The file name must also not be overread: this theorem is a self-adjoint-unitary factorization. It
does **not** formalize Sakai 1.14.4, whose input is a general normal functional and whose polar
factor is a partial isometry with prescribed initial and final support projections.

## Canonical self-adjoint and normal-functional interfaces

For the current specified-predual representation

```lean
f : σ(M, P) →L[ℂ] ℂ,
```

the exact existing condition corresponding to `f* = f` is

```lean
IsSelfAdjoint (WithConv.toConv f).
```

Mathlib's bridge is:

```lean
ContinuousLinearMap.IntrinsicStar.isSelfAdjoint_iff_map_star
    (WithConv.toConv f) :
  IsSelfAdjoint (WithConv.toConv f) ↔
    ∀ x, f (star x) = star (f x).
```

No new `HermitianFunctional` or self-adjoint-functional predicate is needed.

The source theorem genuinely quantifies over the predual, so a specified predual is legitimate in
the source-facing input representation. There is currently no separate bundled type of arbitrary
normal functionals, and this transaction should not create one merely to remove `P` from a type.
Intrinsic results about the resulting positive functionals—support, annihilation, cutdown, and
support orthogonality—should instead be stated for underlying maps `M →ₚ[ℂ] ℂ` with
`IsNormalOnProjections`, where the established API hides the selected predual.

## Existing positive-norm and support inputs

The norm of a positive continuous functional is already available as:

```lean
theorem PositiveContinuousLinearMap.ofReal_opNorm_eq_map_one
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (f : A →P[ℂ] ℂ) :
    ‖(f : A →L[ℂ] ℂ)‖ = f 1
```

This should be reused for every occurrence of `‖fᵢ‖ = fᵢ(1)`. If repeated coercion from a
`PositiveLinearMap` becomes noisy, a thin named bridge may be justified, but the norm theorem
itself must not be reproved.

The exact 1.14.2 interfaces needed for uniqueness and structural orthogonality are:

```text
PositiveLinearMap.apply_eq_zero_iff_le_one_sub_support
PositiveLinearMap.isGreatest_setOf_apply_eq_zero
PositiveLinearMap.apply_mul_support
PositiveLinearMap.apply_support_mul
PositiveLinearMap.apply_support_mul_support
PositiveLinearMap.apply_star_mul_self_eq_zero_iff_mul_support_eq_zero.
```

Their right-annihilator orientation must be preserved:

```text
φ(star x * x) = 0  ↔  x * s(φ) = 0.
```

## Mathlib and original-LeanOA overlap audit

Searches in pinned Mathlib, audited current Mathlib, original LeanOA, and baseline Sak-AI covered:

```text
Jordan decomposition of functionals
positive and negative parts of functionals
self-adjoint / hermitian functionals
orthogonal positive functionals
norm-additive functional differences
functional polar decomposition
functional support and disjoint support
```

No competing or complete reusable implementation was found.

- Mathlib's `MeasureTheory.JordanDecomposition` concerns signed measures and mutual singularity;
  it does not apply to noncommutative $C^*$-algebra functionals.
- Mathlib's positive and negative part notation and CFC APIs concern elements of lattice-ordered
  groups or self-adjoint algebra elements, not dual functionals.
- Mathlib has no lattice/order instance on `PositiveLinearMap` that would identify Sakai's source
  relation with an existing `Disjoint` relation.
- Existing `Disjoint` and `IsOrthogonal` names in Mathlib belong to other principal objects; no
  existing norm-orthogonality relation supplies Definition 1.14.1.
- Mathlib does provide `IsStarProjection.two_mul_sub_one_mem_unitary`, sending a projection `p` to
  the self-adjoint unitary `2 * p - 1`. No reverse packaged theorem splitting a self-adjoint
  unitary into complementary star projections was found in pinned or audited current Mathlib.
- Original LeanOA contains the positive-functional Cauchy--Schwarz layer but contains neither the
  current `Ultraweak.PolarDecomposition` module nor functional support, orthogonality, or Jordan
  decomposition.

The missing mathematics is therefore a small operator-algebraic assembly layer in Sak-AI, not a
new generic ordered-dual foundation.

## Orthogonality API recommendation

Definition 1.14.1 has an immediate consumer in 1.14.3, so one public relation is justified. The
smallest faithful shape is a proposition in namespace `PositiveLinearMap`, defined by the norm of
the existing continuous-linear-map coercion, conceptually:

```lean
def PositiveLinearMap.IsOrthogonal
    (phi psi : A →ₚ[ℂ] ℂ) : Prop :=
  ‖phi.toContinuousLinearMap - psi.toContinuousLinearMap‖ =
    ‖phi.toContinuousLinearMap‖ + ‖psi.toContinuousLinearMap‖
```

This relation needs only the natural $C^*$-algebra/positive-functional context. It should not
require a $W^*$-algebra or normality. The implementation may use nonunital $C^*$-algebra
generality if the existing automatic-continuity API makes that statement clean: the norm relation
itself does not use the unit, while the positive norm formula does. It should not be generalized
to an opaque relation on arbitrary normed-space vectors merely because the displayed equality can
be typed there.

Recommended immediate laws are only those consumed by this transaction:

- symmetry;
- the exact unfolding theorem if the definition is not reducible by design;
- for normal positive functionals on a $W^*$-algebra, the structural characterization

  ```text
  phi.IsOrthogonal psi
    ↔ (phi.support hphi).1 * (psi.support hpsi).1 = 0.
  ```

The product-zero form matches the existing projection API directly and does not rely on accidental
details of the projection-lattice construction. A `Disjoint` corollary may be exposed if it is
short and has a consumer. Support orthogonality remains a theorem, not a second definition.

## Route comparison

### Route A: reuse the existing self-adjoint functional factorization

This is the recommended route.

```text
self-adjoint ultraweak functional f
  -> existing f(x) = phi(u x), with phi positive and u self-adjoint unitary
  -> complementary projections p and q from u
  -> positive ultraweak cutdowns of phi
  -> f = f⁺ - f⁻ and norm additivity
  -> 1.14.2 support cutdowns and uniqueness
  -> support characterization of norm orthogonality
```

The remaining bridges are bounded:

1. Split a self-adjoint unitary into complementary star projections, for example

   ```text
   p = (1 + u) / 2,    q = 1 - p,
   u = p - q.
   ```

   The elementary projection lemma may be general reusable infrastructure if it receives a
   second consumer; otherwise it can remain private to the decomposition module.
2. Use self-adjointness of `f` and positivity of `phi` to prove functional centrality of the
   factor with respect to `u`, hence with respect to `p` and `q`:

   ```text
   phi(u x) = phi(x u).
   ```

   This kills the cross terms and identifies the two pieces with positive two-sided cutdowns.
3. Construct the pieces through existing positive ultraweak cutdown/corner maps, so continuity
   and therefore normality come from established separate-multiplication infrastructure.
4. Obtain norm additivity from the existing positive-functional norm formula and `p + q = 1`.
5. Use 1.14.2 support order/cutdown theorems for uniqueness, following Sakai rather than hiding
   uniqueness behind a choice.

This route reuses the strongest existing analytic input and stays within the settled normality,
support, projection, and continuous-map architectures.

### Route B: build an ordered real-dual Jordan decomposition

This route is not competitive for this transaction.

- Neither pinned nor current Mathlib supplies the necessary ordered-dual Jordan theorem for
  $C^*$-algebra functionals.
- Sak-AI has no lattice structure on the self-adjoint part of the norm dual from which positive
  and negative parts could simply be read off.
- A new ordered-dual construction would still need a separate proof that the parts are normal.
- It would duplicate the difficult norm-attainment/extreme-point work already encapsulated in
  `Ultraweak.exists_positive_comp_mulLeft_of_isSelfAdjoint`.
- It is farther from Sakai's actual proof and creates a larger public architecture with no current
  downstream consumer beyond this theorem.

**Decision: Route A. Do not build Route B in parallel.**

## Exact source-theorem packaging

The source-facing theorem should retain the existing specified-predual representation, because
normality/predual membership is part of Sakai's hypothesis rather than an implementation leak. A
natural theorem-level package has:

```text
f : σ(M,P) →L[ℂ] ℂ
hf : IsSelfAdjoint (WithConv.toConv f)
```

and asserts a unique pair of ordinary positive maps with explicit `IsNormalOnProjections` proofs,
the pulled-back difference, and Sakai's norm orthogonality. This is the accepted production shape:

```lean
∃! parts : (M →ₚ[ℂ] ℂ) × (M →ₚ[ℂ] ℂ),
  parts.1.IsNormalOnProjections ∧
  parts.2.IsNormalOnProjections ∧
  f.comp (Ultraweak.toUltraweakL ℂ M P) =
    parts.1.toContinuousLinearMap - parts.2.toContinuousLinearMap ∧
  parts.1.IsOrthogonal parts.2
```

The norm is necessarily taken after pullback to `M`: the topology synonym `σ(M,P)` is not given
the original operator norm. Ordinary positive witnesses interact directly with the intrinsic
support API. No `NormalFunctional`, `HermitianFunctional`, `JordanDecomposition`, or choice-based
`positivePart` structure is needed for this checkpoint.

Although Sakai writes `f⁺` and `f⁻`, the default for this transaction should remain theorem-level
existence and uniqueness. A later source result may earn named canonical definitions; 1.14.4 does
not require them as data.

## Source fidelity distinctions

The final implementation report and Verso prose should preserve all of the following distinctions.

| Claim | Source status |
| --- | --- |
| Norm equality defines orthogonality | Verbatim mathematical content of Definition 1.14.1 |
| Support-product zero characterizes orthogonality | Derived structural theorem, not the definition |
| `f` is a self-adjoint element of the predual | Verbatim hypothesis of Theorem 1.14.3 |
| The pieces are normal and positive | Verbatim conclusion |
| `f = f⁺ - f⁻` and `‖f‖ = ‖f⁺‖ + ‖f⁻‖` | Verbatim conclusion |
| The decomposition is unique | Verbatim conclusion |
| The parts arise from a self-adjoint unitary factorization | Existing Lean route and substance of the source proof, not part of the theorem statement |
| The positive and negative supports are orthogonal | Derived characterization/consequence |
| Public choice-based definitions `f⁺`, `f⁻` exist | Not required by this source transaction |

## Resolved engineering points and remaining risks

No source-translation blocker was found. The source statement, sign convention, normality
hypothesis, norm identity, and uniqueness assumptions are unambiguous.

Production resolved the bounded Lean engineering points as follows:

1. **Self-adjoint-unitary split:** the reverse projection split remains a private one-consumer
   lemma.
2. **Functional centrality bridge:** self-adjointness is converted to the map-star identity and
   gives the required centrality privately.
3. **Coercion/norm ergonomics:** existing positive-map conversions and the pullback
   `f.comp (toUltraweakL ℂ M P)` are used explicitly; no new functional type is introduced.
4. **Support characterization converse:** uniqueness is proved first from the carrier and cutdown
   equations; the converse is then derived from that theorem, avoiding circularity.
5. **Zero case:** the existing factorization theorem already handles every case, so no new
   normalization split is required.

None of these is missing Mathlib foundational infrastructure of the kind that warrants a new
architecture. In particular, there is no reason to introduce an ordered-dual lattice, a second
functional polar decomposition, a normal-functional wrapper, or a functional calculus.

## Remainder of Section 1.14

After Theorem 1.14.3, exactly one numbered result remains before Section 1.15:

### Theorem 1.14.4

For an arbitrary ultraweakly continuous linear functional `g` on a $W^*$-algebra `M`, Sakai states
a unique polar decomposition

```text
g = R_v phi,
```

where `phi` is normal positive, `‖g‖ = ‖phi‖`, and `v` is a partial isometry whose initial
projection is `s(phi)`. Sakai denotes `phi` by `|g|`, calls it the absolute value, and identifies
the final projection of `v` as `s(|g*|)`.

The section then ends with a historical remark crediting Theorem 1.14.3 to Grothendieck and gives
references; there is no Theorem 1.14.5.

Therefore, after 1.14.1 and 1.14.3 close, the next bounded source transaction is:

```text
Sakai Theorem 1.14.4: polar decomposition of an arbitrary normal functional.
```

That later transaction must audit the exact `R_v` multiplication convention before fixing its
public signature. It must not mistake the existing self-adjoint-unitary factorization for the
general partial-isometry theorem.

## Interface recommendation to the production streams

1. Formalize the exact norm relation of Definition 1.14.1 at positive-functional $C^*$
   generality; do not define it through supports.
2. Prove support-product zero implies norm orthogonality directly; prove Jordan uniqueness from
   carrier and cutdown equations; only then derive the converse and package the characterization.
3. Reuse `Ultraweak.exists_positive_comp_mulLeft_of_isSelfAdjoint` as the only analytic existence
   engine.
4. Keep the self-adjoint-unitary split and functional-centrality facts private unless their
   statements are independently recognizable and reusable.
5. Package the final result theorem-level, with no choice-based positive/negative part definitions.
6. Keep specified-predual data only in the source-facing normal-functional theorem; use the
   intrinsic `PositiveLinearMap.support` API after pulling positive pieces back to `M`.
7. Use the existing positive norm theorem and 1.14.2 greatest-zero/cutdown APIs rather than
   reproving either argument locally.
