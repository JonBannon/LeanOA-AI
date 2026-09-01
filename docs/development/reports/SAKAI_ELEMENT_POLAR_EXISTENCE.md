# Sakai element polar-decomposition existence

Date: 2026-08-31

Workstream: WS-4, Sakai Section 1.12

Baseline: `9476b69357b8d2f6c9884b363f5378098d3ac039`

## Scope and outcome

This workstream proves the existence half of Sakai, Theorem 1.12.1.  For every element `a` of a
$W^*$-algebra it constructs `u` with

```text
a = u * CFC.abs a
star u * u = support |a|
u * star u = support |star a|.
```

The construction uses Sakai's regularized contractions, ultraweak compactness of the closed unit
ball, and his support-defect cutdown `u = q * b * p`.  Uniqueness and final `∃!` packaging remain
deliberately outside WS-4.

## Source proof

Sakai, printed pp. 27--28, first defines

```text
h_n = (star a * a + n⁻¹ 1)^(1/2)
a_n = a * (star a * a + n⁻¹ 1)^(-1/2).
```

He proves that `‖a_n‖ ≤ 1`, `a_n * h_n = a`, and that `h_n` converges uniformly (in norm) to
`|a|`.  It follows that `a_n * |a|` converges in norm to `a`.  Ultraweak compactness of the unit
ball supplies a cluster point `b`, and separate ultraweak continuity of multiplication gives
`b * |a| = a`.

With

```text
p = support |a|
q = support |star a|,
u = q * b * p,
```

Sakai compares `star u * u` with `p`.  Contractivity makes the defect positive, and the equation
obtained after sandwiching that defect by `|a|` forces it to vanish on the support.  Hence
`star u * u = p`.  The resulting partial-isometry identity and the left-support universal
property then identify `u * star u` with `q`.

The Lean proof follows this route.  Sakai compresses the existence defect step to the sentence that
`‖b‖ ≤ 1` implies `p = p * star b * q * b * p`; Lean expands that implication through positivity,
square-root zero detection, and the already established theorem
`WStarAlgebra.mul_support_eq_zero_iff`.  Sakai's separate closed-right-ideal argument occurs later,
in uniqueness, and is not used in WS-4.

## Production regularizer

`LeanOA.Ultraweak.ElementPolarDecomposition` imports no file from `Scratch`.  It privately
reconstructs the checked WS-3 regularizer, reindexing Sakai's positive integers by

```text
epsilon n = ((n + 1 : ℝ)⁻¹)
c a n = star a * a + epsilon n • 1
h a n = CFC.sqrt (c a n)
regularizer a n = a * (c a n) ^ (-(1 / 2 : ℝ)).
```

The private production lemmas prove:

- positivity and strict positivity of `c a n`;
- the exact conjugated formula for `star (regularizer a n) * regularizer a n`;
- `‖regularizer a n‖ ≤ 1` and unit-closed-ball membership;
- `regularizer a n * h a n = a`;
- norm convergence `h a n → CFC.abs a`;
- norm convergence `regularizer a n * CFC.abs a → a`.

Only the source-facing existence theorem is public; the indexing and regularization choices do not
constrain the later API.

## Ultraweak compactness

The implementation internally chooses

```text
P := WStarAlgebra.predual M
```

and regards the regularizer as a map into `σ(M, P)`.  The pointwise unit-ball estimate gives

```text
map (fun n => toUltraweak ℂ P (regularizer a n)) atTop
  ≤ principal (ofUltraweak ⁻¹' Metric.closedBall 0 1).
```

`Ultraweak.isCompact_closedBall` and `IsCompact.exists_mapClusterPt` therefore supply an
ultraweak cluster point `bσ` in that ball.  Setting `b = ofUltraweak bσ` gives `‖b‖ ≤ 1`.

No sequential-compactness or first-countability assertion is used.  The proof extracts an
ultrafilter refining `atTop` through `mapClusterPt_iff_ultrafilter`.  Thus the topology is exactly
the weak-* / ultraweak topology `σ(M, P)`, not the strong topology from Section 1.11 and not the
Banach-space weak topology.

## Cluster equation

Along the refining ultrafilter, separate ultraweak continuity supplies

```text
regularizer a n * CFC.abs a → b * CFC.abs a
```

through fixed-right multiplication.  The independently proved norm convergence maps into the
ultraweak topology and gives the same net the limit `a`.  Hausdorff uniqueness of limits yields

```text
b * CFC.abs a = a.
```

The implementation uses only the existing semitopological-ring/fixed-multiplication API; it does
not assume joint ultraweak continuity.

## Cutdown

The private cutdown theorem defines

```text
x := CFC.abs a
p := support ⟨x, (CFC.abs_nonneg a).isSelfAdjoint⟩
q := support ⟨CFC.abs (star a), (CFC.abs_nonneg (star a)).isSelfAdjoint⟩
u := q.1 * b * p.1.
```

The accepted bridges identify `p` with `rightSupport a` and `q` with `leftSupport a`.  Consequently
`p` fixes `x` on both sides and `q` fixes `a` on the left.  These facts and `b * x = a` prove

```text
u * x = a.
```

## Initial support

From `‖b‖ ≤ 1`, the proof obtains

```text
star b * b ≤ 1
star b * q.1 * b ≤ 1
star u * u ≤ p.1.
```

Hence `d = p.1 - star u * u` is nonnegative.  Factorization and
`CFC.abs_mul_abs` give

```text
x * d * x = 0.
```

Writing `d` as `CFC.sqrt d * CFC.sqrt d`, C-star zero detection gives
`d * x = 0`.  The stable support-kernel equivalence

```text
WStarAlgebra.mul_support_eq_zero_iff
```

then gives `d * p.1 = 0`.  Since `u * p.1 = u`, expansion of this last equality proves

```text
star u * u = p.1.
```

This is the exact source initial-support equation.

## Final support

The initial equation makes `star u * u` a star projection.  The accepted general theorem
`IsStarProjection.mul_star_self` therefore shows that `u * star u` is a star projection.

Because `q.1 * u = u`, its projection lies below `q`.  Conversely,
`IsStarProjection.mul_star_mul_self` shows that `u * star u` fixes `a = u * |a|` on the left.
The universal property `WStarAlgebra.leftSupport_le_iff`, together with
`WStarAlgebra.support_abs_star`, gives the reverse inequality.  Therefore

```text
u * star u = q.1.
```

Sakai instead writes the intermediate identity
`a * star a = u * (star a * a) * star u` and concludes `u * p * star u = q`.  Lean proves that
source identity separately below, but uses the equivalent support-universal-property argument for
the final equality because it is shorter against the established API.  No symmetry shortcut, PVM,
or spectral-integral machinery is used.

## Partial-isometry identities

The equality `star u * u = p.1` immediately provides `IsStarProjection (star u * u)`.  The existing
production API then gives

```text
u * star u * u = u
u * (star u * u) = u
IsStarProjection (u * star u).
```

No new partial-isometry predicate or bundled polar-decomposition object was introduced.

## Source identity

The generally reusable identity was added at the weaker abstract nonunital real-CFC generality of
Mathlib's `CFC.abs_mul_abs` to `LeanOA.Mathlib.Analysis.CStarAlgebra.Abs`:

```lean
CFC.mul_star_eq_of_eq_mul_abs
    (h : a = u * CFC.abs a) :
    a * star a = u * (star a * a) * star u
```

It uses only factorization, self-adjointness of `CFC.abs a`, and `CFC.abs_mul_abs`; it carries no
norm, $C^*$-algebra, $W^*$-algebra, or unital hypothesis.

## Public theorem

The public WS-4 declaration is:

```lean
WStarAlgebra.exists_element_polar_decomposition
    {M : Type*}
    [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] [WStarAlgebra M]
    (a : M) :
    ∃ u : M,
      a = u * CFC.abs a ∧
      star u * u =
        (WStarAlgebra.support
          ⟨CFC.abs a, (CFC.abs_nonneg a).isSelfAdjoint⟩).1 ∧
      u * star u =
        (WStarAlgebra.support
          ⟨CFC.abs (star a),
            (CFC.abs_nonneg (star a)).isSelfAdjoint⟩).1
```

The chosen predual, regularizer, cluster filter, and cutdown scaffolding do not appear in the
signature.

## WS-5 readiness

WS-5 must prove uniqueness of `u` under the factorization and initial-support condition, package
the exact source theorem as `∃!`, choose the final source-facing theorem name, and connect it to
Verso.  Existence, both source support equations, partial-isometry consequences, and the source
`a * star a` identity are now available without placeholders.

## Architecture and integrity

```text
CFC.abs canonical: yes
Scratch imported by production: no
ordinary WStarAlgebra public context: yes
chosen predual exposed publicly: no
PVM used: no
spectral integral used: no
joint ultraweak multiplication assumed: no
duplicate partial-isometry predicate introduced: no
```

Focused validation:

```text
lake env lean LeanOA/Mathlib/Analysis/CStarAlgebra/Abs.lean
lake env lean LeanOA/Ultraweak/ElementPolarDecomposition.lean
lake build LeanOA.Mathlib.Analysis.CStarAlgebra.Abs \
  LeanOA.Ultraweak.ElementPolarDecomposition
```

The build succeeds.  `#print axioms` reports exactly

```text
[propext, Classical.choice, Quot.sound]
```

for both `CFC.mul_star_eq_of_eq_mul_abs` and
`WStarAlgebra.exists_element_polar_decomposition`.

```text
CUSTOM AXIOMS ADDED: 0
SORRY/ADMIT ADDED: 0
OTHER MATHEMATICAL PLACEHOLDERS ADDED: 0
```

Assessment: **IMPROVED — SOURCE EXISTENCE THEOREM / MATHLIB REUSE / COMBINATION**.
