# Sakai 1.14.2: functional-support source and architecture audit

## Status and scope

This is the WS-14A source/architecture report for Sakai, Definition 1.14.2. It records the
source theorem, fixes the left/right orientation, audits the available libraries, and justifies
the one accepted public support signature. The production implementation and validation are
recorded separately in `SAKAI_1_14_2_FUNCTIONAL_SUPPORT.md`; no second functional-support
construction is approved.

Baseline audited:

```text
Sak-AI                  05c69abaa5a8608700a75d25b4da05d04d63a588
pinned Mathlib          476ab284693e554a6b48c5f5210cb4fb5ae51252
audited current Mathlib 567908cf509fb0bab796e5401edf35b4492ae48f
original LeanOA         cb811c1006ae78a0ff1d175253200e1859843370
```

The governing reuse requirement for this work is:

> Before introducing any new foundational theorem or proof pattern, search Mathlib, search the original LeanOA repository, and search the current Sak-AI repository for an existing theorem, definition, abstraction, or argument that already supplies the needed mathematics; reuse it where mathematically faithful, preserve architectural continuity with the APIs already built, and generalize only when that genuinely improves portability or reuse rather than duplicating local infrastructure.

## Source reconstruction

Source: Sakai, *C*-Algebras and *W*-Algebras*, Section 1.14, printed p. 31 (local
`SakaiBook_1971.pdf`, PDF p. 43).  The classification facts used by the source occur at printed
pp. 21 and 24--25 (PDF pp. 33 and 36--37).

### Preceding definition

Definition 1.14.1 calls two positive functionals `φ₁` and `φ₂` orthogonal when

```text
‖φ₁ - φ₂‖ = ‖φ₁‖ + ‖φ₂‖.
```

This definition is not needed to construct functional support, but it is the next input to
Theorem 1.14.3.

### Definition 1.14.2

Let `φ` be a **normal positive linear functional** on a $W^*$-algebra `M`, and set

```text
Lφ = {x ∈ M | φ (x* x) = 0}.
```

The source then records the following chain.

1. `Lφ` is a left ideal.
2. `Lφ` is closed for the strong topology `s(M,M*)`.
3. Therefore `Lφ` is closed for the weak-star/ultraweak topology `σ(M,M*)`.
4. Consequently there is a projection `p₀` such that `Lφ = M p₀`.
5. `p₀` is the greatest projection `q` for which `φ(q) = 0`.
6. The support is the complementary projection

   ```text
   s(φ) = 1 - p₀.
   ```

7. For every `x ∈ M`, the source gives all three cutdown forms:

   ```text
   φ(x) = φ(s(φ) x) = φ(x s(φ)) = φ(s(φ) x s(φ)).
   ```

8. The source calls `φ` faithful when `s(φ) = 1`.  It also calls a family `{φᵢ}` faithful when
   simultaneous vanishing `φᵢ(x* x) = 0` for every `i` forces `x = 0`.

The hypotheses are exactly as follows.

| Property | Assumed? |
| --- | --- |
| positive | yes |
| normal | yes |
| linear and bounded | yes, through “positive linear functional” |
| $W^*$-algebra domain | yes |
| nonzero | no |
| normalized/state | no |
| faithful | no; this is characterized after support is defined |

There is no centrality assertion for `s(φ)`.

### Topology and classifier used by the source

The source order is important: **strong closedness first, ultraweak closedness second**.

- Sakai 1.8.11 says that the `s(M,M*)`- and `σ(M,M*)`-closures of a convex subset of `M`
  agree (as part of a larger list of equivalent closure conditions).  A left ideal is convex, so
  this is the cited bridge from strong to ultraweak closedness.
- Sakai 1.10.1 classifies a `σ(M,M*)`-closed left ideal as `M p` for a unique projection `p`
  (and a closed right ideal as `q M`).  This is the projection-generation result used in 1.14.2.

In the current Lean topology vocabulary, these are `s(M, P)` in `Ultraweak.Strong` and
`σ(M, P)` in `Ultraweak`, with a specified predual `P` only while making a topology-dependent
statement.

### Exact orientation

The ideal is a **left** ideal and is generated on the **right**:

```text
Lφ = M p₀.
```

Since `s(φ) = 1 - p₀`, the intrinsic annihilator statement is therefore

```text
x ∈ Lφ  ↔  x * s(φ) = 0,
```

equivalently

```text
x ∈ Lφ  ↔  x = x * (1 - s(φ)).
```

The formulas with `s(φ) * x = 0`, `p₀ M`, or a right ideal have the wrong orientation for
Sakai's `Lφ`.

### Faithfulness: source statement versus derived corner theorem

Definition 1.14.2 defines global faithfulness by `s(φ) = 1` and defines faithful families by a
common quadratic kernel.  It does **not** explicitly state in this paragraph that the restriction
of `φ` to `s(φ) M s(φ)` is faithful.

Faithfulness on the support corner is nevertheless an immediate, useful derived theorem.  If
`x ∈ s(φ) M s(φ)` and `φ(x* x) = 0`, then `x ∈ Lφ`, hence `x s(φ) = 0`; the corner identity
`x s(φ) = x` gives `x = 0`.  The production report should label this as a derived support-corner
consequence, not as verbatim source text.

### Downstream use in Section 1.14

- Theorem 1.14.3 uses supports in the uniqueness analysis for the orthogonal positive/negative
  parts of a self-adjoint predual functional.
- Theorem 1.14.4 uses `s(φ)` as the initial projection of the partial isometry in the polar
  decomposition of a normal functional.  Its uniqueness argument uses the greatest-zero
  characterization: from vanishing on a complementary projection it concludes that `s(φ)` lies
  below the competing initial projection.

Thus the annihilator and greatest-zero theorems, rather than the internal choice of `p₀`, are the
right abstraction boundary for later Section 1.14 proofs.

## Library audit

Searches covered positive-functional support, functional faithfulness, GNS null spaces,
one-sided ideals, ultraweakly closed ideals, projection-generated ideals, element support,
corners, cutdowns, normality, and positive-functional Cauchy--Schwarz.

### Pinned and current Mathlib

Neither the pinned Mathlib nor the audited current Mathlib contains a support projection or
faithfulness API for a positive functional on a $W^*$-algebra. In particular, no existing
`nullIdeal`, functional-support definition, or applicable positive-functional `Faithful`
predicate was found.

Mathlib does supply reusable GNS infrastructure in
`Mathlib/Analysis/CStarAlgebra/GelfandNaimarkSegal.lean`, notably:

- `PositiveLinearMap.PreGNS`;
- `PositiveLinearMap.toPreGNS` and `PositiveLinearMap.ofPreGNS`;
- `PositiveLinearMap.leftMulMapPreGNS`.

`leftMulMapPreGNS` packages bounded left multiplication for the GNS seminorm.  It is useful
background for the algebraic closure of the null space, but there is no reason to turn this
transaction into a new GNS architecture.

### Original LeanOA

Original LeanOA contains the positive-functional Cauchy--Schwarz layer in
`LeanOA/CStarAlgebra/PositiveLinearFunctional.lean`.  It does not contain the current Sak-AI
functional-support construction, the current projection classifier, or an equivalent
positive-functional null-ideal/support API.  It therefore supplies an argument to reuse, not a
definition to duplicate.

### Current Sak-AI infrastructure to reuse

The following declarations are directly relevant and already establish the needed semantic
core:

| Declaration | Role |
| --- | --- |
| `PositiveLinearMap.cauchy_schwarz_star_mul` | canonical coefficient estimate |
| `PositiveLinearMap.cauchy_schwarz_mul_star` | adjoint-oriented coefficient estimate |
| `PositiveLinearMap.gnsSeminorm` / `gnsSeminorm_apply` | exact seminorm whose zero set is `Lφ` |
| `PositiveLinearMap.IsNormalOnProjections` | settled normality predicate |
| `PositiveLinearMap.isNormalOnProjections_iff_mem_continuousDual` | normality-to-ultraweak-continuity bridge |
| `Ultraweak.Strong.seminorm` / `seminorm_apply` | defining strong seminorm for a normal positive functional |
| `Ultraweak.Strong.withSeminorms` | continuity of the defining strong seminorms |
| `Ultraweak.Strong.image_closure_toUltraweakEquiv` | formal Sakai 1.8.11 closure bridge for real-convex sets |
| `Ideal.existsUnique_isStarProjection_eq_span_of_isClosed_ultraweak` | exact closed-left-ideal classifier |
| `Ideal.range_mulRight` | identifies `Ideal.span {p}` with the range `M p` |
| `IsStarProjection.span_singleton_le_span_singleton_iff` | turns ideal inclusion into projection order |
| `IsStarProjection.orderIsoUltraweakClosedIdeal` | reusable packaged projection/closed-ideal equivalence |
| `WStarAlgebra.leftSupport`, `rightSupport`, `support` | existing **element** support; must remain distinct |
| `IsStarProjection.Corner`, `inclusionP`, `cutdownP` | established corner and cutdown API |
| `IsStarProjection.Corner.projection_mul`, `mul_projection` | support-corner identity laws |

There is no missing one-sided-ideal classifier and no justification for rebuilding it.

The current `WStarAlgebra.leftSupport`, `rightSupport`, and `support` take algebra elements (the
last takes a self-adjoint element).  A functional support belongs in namespace
`PositiveLinearMap`; this resolves the name collision by type and namespace without attempting a
spurious common wrapper.

### Accepted production interface and probes

The accepted implementation is `LeanOA/Ultraweak/FunctionalSupport.lean`. Its relevant public
names are:

```text
PositiveLinearMap.nullIdeal
PositiveLinearMap.mem_nullIdeal
PositiveLinearMap.mem_nullIdeal_iff_forall_apply_star_mul_eq_zero
PositiveLinearMap.IsNormalOnProjections.isClosed_nullIdeal_strong
PositiveLinearMap.IsNormalOnProjections.isClosed_nullIdeal_ultraweak
PositiveLinearMap.support
PositiveLinearMap.nullIdeal_eq_span_one_sub_support
PositiveLinearMap.mem_nullIdeal_iff_mul_support_eq_zero
PositiveLinearMap.apply_star_mul_self_eq_zero_iff_mul_support_eq_zero
PositiveLinearMap.apply_eq_zero_iff_le_one_sub_support
PositiveLinearMap.isGreatest_setOf_apply_eq_zero
PositiveLinearMap.apply_mul_support
PositiveLinearMap.apply_support_mul
PositiveLinearMap.apply_support_mul_support
PositiveLinearMap.support_eq_one_iff_apply_star_mul_self_eq_zero_imp
PositiveLinearMap.apply_star_mul_self_eq_zero_iff_on_support_corner
PositiveLinearMap.apply_eq_zero_iff_of_nonneg_on_support_corner
```

Independently, scratch work kernel-checked a factored variant through
`restrictScalars_nullIdeal_eq_iInf_ker_gnsCoefficient`,
`gnsCoefficient_mem_continuousDual_of_mem_continuousDual`, and
`Ultraweak.isClosed_iInf_ofSubmodule`. The accepted production theorem instead follows Sakai's
source order: it first proves strong closedness as the zero set of
`Ultraweak.Strong.seminorm`, then transports closure through
`Ultraweak.Strong.image_closure_toUltraweakEquiv` using real convexity. The direct kernel proof
remains only a discarded scratch comparison.

## Route comparison

### Route A: Sakai's null-left-ideal route

This route is both source-faithful and well supported by the existing code.

1. Define `Lφ` for every positive functional at C-star-algebra generality.
2. Use Cauchy--Schwarz to identify membership with vanishing of every coefficient
   `φ(y* x)` and to prove the left-ideal laws.
3. Under normality, realize `φ` as an ultraweakly continuous positive functional for the chosen
   predual.
4. Prove strong closedness as the zero set of the defining strong seminorm attached to `φ`.
5. Use `Ultraweak.Strong.image_closure_toUltraweakEquiv` and convexity of the ideal to obtain
   ultraweak closedness, exactly following 1.8.11.  The independently checked intersection-of-
   kernels argument is a valid fallback or supplementary direct proof, but should not replace
   the source strong-closed statement if 1.14.2 is marked source-formalized.
6. Apply `Ideal.existsUnique_isStarProjection_eq_span_of_isClosed_ultraweak` once.
7. Define support as the complement of that unique generator.

This route needs normality only from Step 3 onward.  The null ideal and its Cauchy--Schwarz API
remain reusable for arbitrary positive functionals on a C-star algebra.

### Route B: supremum or maximal family of zero projections

This route is not competitive as the foundational construction.

Let `Zφ = {q projection | φ(q) = 0}`.  Although the projection lattice is complete and Section
1.13 supplies complete additivity on orthogonal families, the missing step is not the existence
of a supremum.  One must prove that the supremum is still `φ`-zero.

- `Zφ` is not visibly directed: arbitrary zero projections need not commute, and complete
  additivity applies to orthogonal families rather than arbitrary joins.
- A maximal orthogonal zero family does not solve maximality.  In a non-distributive projection
  lattice, `q ≰ p` does not imply `q ∧ (1-p) ≠ 0`.
- Extracting a nonzero zero projection orthogonal to `p` from such a `q` requires support/polar
  decomposition or null-left-ideal machinery.  That recreates the route one was trying to avoid.
- Proving that finite or arbitrary joins of zero projections remain zero likewise naturally
  passes through coefficient vanishing and the closed null ideal.

After Route A is complete, `p₀` may harmlessly be characterized as `sSup Zφ`; greatestness makes
that a derived order theorem.  It should not be a second definition.  Section 1.13 complete
additivity is therefore not needed for the first support construction, and omitting it here is
reuse discipline rather than duplication.

**Decision:** use Route A.  Do not develop Route B in parallel.

## Recommended definition architecture

### Null ideal

The reusable general definition should be:

```lean
def PositiveLinearMap.nullIdeal
    (φ : A →ₚ[ℂ] ℂ) : Ideal A
```

under the weakest natural assumptions that support Mathlib's unital `Ideal A` and the
positive-functional Cauchy--Schwarz theorem (in current Sak-AI, `CStarAlgebra A`,
`PartialOrder A`, and `StarOrderedRing A`).  Its defining simp theorem should be

```lean
@[simp] theorem PositiveLinearMap.mem_nullIdeal (x : A) :
    x ∈ φ.nullIdeal ↔ φ (star x * x) = 0
```

and the coefficient characterization is sufficiently reusable to publish:

```lean
theorem PositiveLinearMap.mem_nullIdeal_iff_forall_apply_star_mul_eq_zero (x : A) :
    x ∈ φ.nullIdeal ↔ ∀ y : A, φ (star y * x) = 0
```

No normality or $W^*$-structure belongs on these declarations.

### Functional support

Normality is mathematically necessary for the support to be an internal projection of `M` by
this construction. A singular positive functional on a $W^*$-algebra need not have an
ultraweakly closed null ideal, so a total definition on all positive functionals would be
misleading.  The project also explicitly rules out a second bundled normal-functional type.

The smallest honest intrinsic signature is therefore:

```lean
noncomputable def PositiveLinearMap.support
    (φ : M →ₚ[ℂ] ℂ) (hφ : φ.IsNormalOnProjections) :
    {p : M // IsStarProjection p}
```

in the ordinary existing `WStarAlgebra M` context.  The implementation may select
`WStarAlgebra.predual M` internally, prove `φ.nullIdeal` closed, choose the unique generator
`p₀`, and return `1-p₀`.  Proof irrelevance and uniqueness make the result intrinsic.

Rejected alternatives:

- do not define `support` for every positive functional by returning an arbitrary/default
  projection when normality fails;
- do not hide normality in a new `Fact` instance;
- do not introduce a new bundled `NormalPositiveFunctional` merely to improve dot notation;
- do not publish the generator as a second `nullSupport` definition;
- do not expose `P` in `support` or its intrinsic characterizations.

Topology-specific helper theorems should retain explicit `P`, because their statements really
mention `s(M,P)` or `σ(M,P)`.  This is the correct place for selected-predual visibility.

## Smallest stable public theorem layer

Beyond `nullIdeal`, one support definition and the following theorem families are enough.  The
names below are the recommended naming target; the mathematical signatures and orientations are
the essential decision.

### Topological inputs

```lean
theorem PositiveLinearMap.IsNormalOnProjections.isClosed_nullIdeal_strong
    (hφ : φ.IsNormalOnProjections) :
    IsClosed (Ultraweak.ofStrong ⁻¹' (φ.nullIdeal : Set M) : Set s(M, P))

theorem PositiveLinearMap.IsNormalOnProjections.isClosed_nullIdeal_ultraweak
    (hφ : φ.IsNormalOnProjections) :
    IsClosed (Ultraweak.ofSubmodule (P := P)
      (φ.nullIdeal.restrictScalars ℂ) : Set σ(M, P))
```

Only these topology-facing theorems expose `P`.  The exact strong-set spelling may be adjusted to
the established synonym/transport lemmas, but the source assertion itself should remain public.

### Zero projections and annihilation

For `q : {q : M // IsStarProjection q}`:

```lean
theorem PositiveLinearMap.apply_projection_eq_zero_iff_le_one_sub_support :
    φ q.1 = 0 ↔ q.1 ≤ 1 - (φ.support hφ).1

@[simp] theorem PositiveLinearMap.mem_nullIdeal_iff_mul_support_eq_zero (x : M) :
    x ∈ φ.nullIdeal ↔ x * (φ.support hφ).1 = 0
```

The first theorem is the stable greatest-zero-projection API.  The second hides all ideal-choice
details from downstream proofs.  An equivalent theorem
`x ∈ φ.nullIdeal ↔ x = x * (1 - (φ.support hφ).1)` is useful only if it acquires an immediate
consumer; it need not be part of the first public surface.

### Source cutdown identities

All three variants are explicitly recorded by Sakai and are useful simp/rewrite endpoints:

```lean
@[simp] theorem PositiveLinearMap.apply_support_mul (x : M) :
    φ ((φ.support hφ).1 * x) = φ x

@[simp] theorem PositiveLinearMap.apply_mul_support (x : M) :
    φ (x * (φ.support hφ).1) = φ x

theorem PositiveLinearMap.apply_support_mul_support (x : M) :
    φ ((φ.support hφ).1 * x * (φ.support hφ).1) = φ x
```

The one-sided identities are simp rules. The two-sided identity is a named rewrite theorem but is
not separately tagged `simp`, because the one-sided rules already normalize its left-hand side.
These are cutdown identities, not commutation or centrality claims.

### Faithfulness

No canonical positive-map `Faithful` predicate was found in Mathlib, original LeanOA, or Sak-AI.
The first public layer should therefore use theorem statements, not a new structure or class:

```lean
theorem PositiveLinearMap.support_eq_one_iff :
    (φ.support hφ).1 = 1 ↔
      ∀ x : M, φ (star x * x) = 0 → x = 0
```

For the derived corner theorem, reuse `IsStarProjection.Corner` and state that an element of the
support corner with zero quadratic value is zero.  If the corner theorem has no immediate
downstream consumer in 1.14.3, it may remain a named theorem without introducing a restricted
positive-map definition.

The source's faithful-family definition can be formalized when a later result consumes it; it is
not required to define the support itself.

## Proof obligations and blockers

### Closed or routine engineering

- The Cauchy--Schwarz zero-coefficient lemmas and null-left-ideal laws are routine and have been
  kernel-checked in the current WS-14 probes.
- Direct ultraweak closedness through an intersection of coefficient kernels has been
  kernel-checked.
- The existing closed-left-ideal classifier exactly matches the required orientation.
- The greatest-zero and right-annihilator steps have kernel-checked scratch prototypes.
- Existing corner multiplication laws close the derived support-corner faithfulness argument
  once the annihilator theorem is available.

### Exact-source obligation closed

The production strong-closedness theorem constructs the positive ultraweakly continuous
realization of `φ`, identifies `Lφ` with the zero set of `Ultraweak.Strong.seminorm`, and uses
`Ultraweak.Strong.withSeminorms`. The production ultraweak theorem then applies the established
real-convex closure bridge, exactly reflecting Sakai's citation of 1.8.11. Final command results
belong to the production report rather than this source audit.

### Architectural approval

The lead accepted the explicit normality-proof argument in
`PositiveLinearMap.support φ hφ`. The rejected alternatives would either misstate the domain of
support, expose an implementation predual, or create a competing normal-functional wrapper.

### Blocker classification

| Item | Classification | Severity |
| --- | --- | --- |
| strong zero-set spelling and closure transport | mere engineering work | small |
| hiding the chosen predual inside intrinsic `support` | mere engineering work; established pattern | small |
| support signature approval | architectural decision | bounded |
| functional-support API in Mathlib | absent, but local infrastructure suffices | not blocking |
| closed one-sided-ideal classifier | already in Sak-AI | no blocker |
| source left/right orientation | resolved | no blocker |
| source faithfulness wording | resolved; corner version is derived | no blocker |
| Route B arbitrary-join argument | mathematical/formalization detour | avoid |

## Decision summary

1. Sakai's ideal is `Lφ = {x | φ(x* x)=0}`, a left ideal of the form `M p₀`.
2. `p₀` is the greatest `φ`-zero projection and `s(φ)=1-p₀`.
3. The intrinsic nullity test is `x * s(φ)=0`, not `s(φ) * x=0`.
4. Use the null-left-ideal route and the existing ultraweak closed-ideal classifier.
5. Preserve strong closedness as an exact source assertion; direct ultraweak closedness is a
   checked shortcut but not a substitute for that assertion in a source-complete report.
6. Put functional support in `PositiveLinearMap`, separate from `WStarAlgebra.support` for
   elements.
7. Define `nullIdeal` generally, but require explicit normality for functional support.
8. Hide the canonical $W^*$-predual from `support` and all intrinsic support theorems.
9. Publish no second null-support projection and no new faithfulness/normal-functional structure.
10. The support signature and orientation are settled; no source, mathematical, or architectural
    blocker remains for Definition 1.14.2.
