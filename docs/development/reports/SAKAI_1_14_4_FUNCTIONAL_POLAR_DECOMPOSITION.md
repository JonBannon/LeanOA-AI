# Sakai 1.14.4: general polar decomposition of a normal functional

## Result

`LeanOA/Ultraweak/FunctionalPolarDecomposition.lean` formalizes Sakai, Theorem 1.14.4 for an
arbitrary normal functional on a $W^*$-algebra.  The exact source reconstruction, including the
right-action convention, is in `SAKAI_1_14_4_SOURCE.md`.

The source-facing theorem is

```text
Ultraweak.existsUnique_functional_polar_decomposition.
```

For `g : sigma(M,P) ->L[ℂ] ℂ`, it gives a unique pair `(v, phi)` where `phi` is normal positive,

```text
g.comp (toUltraweakL ℂ M P) = phi.cutoff v,
‖g.comp (toUltraweakL ℂ M P)‖ = ‖phi.toContinuousLinearMap‖,
star v * v = support phi,
v * star v = support (functionalAbs g*).
```

Since `phi.cutoff v x = phi (x * v)`, this is exactly Sakai's `g = R_v phi` convention.

## Existing Sak-AI theorem and reconciliation

The pre-existing public theorem in `Ultraweak.PolarDecomposition` is

```text
Ultraweak.exists_positive_comp_mulLeft_of_isSelfAdjoint.
```

It says that a **self-adjoint** ultraweakly continuous functional factors as `phi(u * x)`, where
`u` is a self-adjoint unitary and `phi` is positive and ultraweakly continuous.  Its proof already
contains the relevant compact exposed-face/Krein--Milman mechanism.  It was an architectural and
analytic prototype, not an implementation of Theorem 1.14.4.

| Sakai 1.14.4 requirement | Earlier `PolarDecomposition` | Production result | Bridge / decision |
| --- | --- | --- | --- |
| arbitrary normal `g` | self-adjoint `g` only | arbitrary `g` | extend the same exposed-face method to the full unit ball |
| `R_v phi`, hence `phi(x v)` | left factor `phi(u x)` | `phi.cutoff v`, hence `phi(x v)` | use the established right-action API explicitly |
| partial isometry | self-adjoint unitary | `star v * v` is the support projection | trim the exposed extreme point by functional support |
| normal positive factor | positive ultraweak map | ordinary positive map plus `IsNormalOnProjections` | reuse the settled pullback/normality bridge |
| norm equality | not exposed publicly | exact operator-norm equality | retain the norm-attaining calculation |
| initial support | absent | `star v * v = support phi` | reuse Section 1.14.2 support |
| final support | absent | `v * star v = support (functionalAbs g*)` | conjugate the positive factor and invoke uniqueness for `g*` |
| uniqueness | absent | unique pair | support cutdown and null-ideal argument |

The implementation therefore does not pretend that the old self-adjoint/left/unitary theorem is
already the source result, but it also does not create a competing functional type or
factorization hierarchy.  It is a downstream, direct exposed-face extension using the same
topological and C-star-algebra infrastructure.  The Jordan decomposition is not used merely
because it is available.

## Construction and support trimming

The private existence engine exposes the full closed unit ball by the real part of `g`.  An
extreme point `u` supplies a positive right translate with the correct norm.  If `q` is the
support of that positive functional, the multiplier is trimmed to

```text
v = star u * q.
```

The extreme-point projection equations and the support cutdown identities then give

```text
star v * v = q
```

and the exact right factorization.  A C-star-algebraic large-parameter estimate proves the
remaining final-cutdown identity needed to recover `g`; it remains private because it is an
implementation lemma rather than a Section 1.14 API endpoint.

The proof applies to the zero functional and to subsingleton algebras.  No nonzero hypothesis is
leaked into the public theorem.

## Normality and reusable conjugation

Two small reusable bridges were promoted rather than duplicated locally.

- `PositiveContinuousLinearMap.comp_toUltraweakPosCLM_isNormalOnProjections` records that pulling
  a positive ultraweak functional back to the underlying algebra produces a normal positive
  functional.
- `PositiveLinearMap.IsNormalOnProjections.conjugate` records that
  `x |-> phi(a* x a)` remains normal.

The underlying operation

```text
PositiveLinearMap.conjugate phi a x = phi (star a * x * a)
```

is defined in the ordinary positive-functional API at nonunital C-star-algebra generality.  It
does not depend on a predual or $W^*$ structure; only its normality theorem does.  This is the
weakest natural placement and makes the bridge reusable outside this source theorem.

## Uniqueness

Suppose two pairs `(v, phi)` and `(w, psi)` have the same right factorization, norm, normality,
and initial-support equations.  The proof first compares the two supports using
`support_le_iff_apply_eq_apply_one`, in both directions.  Once the supports agree, it expands

```text
phi (star (v - w) * (v - w))
```

and uses the norm identities to show that this value is zero.  The Section 1.14.2 null-ideal
criterion implies `(v - w) * support(phi) = 0`; the initial-projection equations reduce this to
`v = w`.  Support cutdown and the common factorization then give `phi = psi`.

Thus `existsUnique_functional_polar_decomposition_basic` proves uniqueness of the entire pair,
not only uniqueness of the positive factor.  The final-projection condition is subsequently
added to the same unique pair by the source-facing theorem.

## Canonical positive factor

Decision:

```text
DECISION: publish the canonical functional absolute value.
```

Sakai immediately denotes the unique positive factor by `|g|`, and the final-projection clause
itself refers to `|g*|`.  The production definition `Ultraweak.functionalAbs` is therefore earned
by immediate source use.  It is introduced only after the unique normalized factorization has
been proved; it is not an arbitrary choice masquerading as a canonical object.

The supporting API is:

- `Ultraweak.functionalAbs_isNormalOnProjections`;
- `Ultraweak.functionalAbs_spec`;
- `Ultraweak.norm_functionalAbs`;
- `Ultraweak.eq_functionalAbs_of_polar_decomposition`.

These lemmas expose normality, existence of a multiplier, norm preservation, and the uniqueness
eliminator without exposing private witnesses.

## Final projection

For a normalized factorization `g = R_v phi`, the positive factor for `g*` is conjugation of
`phi` by `v`.  The reusable theorem

```text
PositiveLinearMap.support_conjugate_eq_mul_star
```

identifies its support with `v * star v`.  Uniqueness then identifies that conjugated functional
with `functionalAbs g*`, yielding

```text
Ultraweak.functional_polar_decomposition_final_projection.
```

This theorem is also included as a clause of
`Ultraweak.existsUnique_functional_polar_decomposition`, so the exact source theorem does not
silently omit Sakai's final-support assertion.

## Partial-isometry decision

Decision:

```text
DECISION: continue expressing partial isometry through projection equations.
```

No suitable established public `IsPartialIsometry` predicate was found in pinned Mathlib,
audited current Mathlib, original LeanOA, or the current tree.  The equation

```text
star v * v = support phi
```

already says that the initial product is a star projection and supplies the established
partial-isometry semantics.  The final-support theorem supplies the corresponding final
projection.  A new predicate would only wrap these equations in this transaction and would not
improve interoperability.

## Public API

The public theorem/definition surface introduced or promoted for this wave is:

- `PositiveLinearMap.conjugate` and `PositiveLinearMap.conjugate_apply`;
- `PositiveContinuousLinearMap.comp_toUltraweakPosCLM_isNormalOnProjections`;
- `PositiveLinearMap.IsNormalOnProjections.conjugate`;
- `PositiveLinearMap.support_conjugate_eq_mul_star`;
- `Ultraweak.existsUnique_functional_polar_decomposition_basic`;
- `Ultraweak.functionalAbs`;
- `Ultraweak.functionalAbs_isNormalOnProjections`;
- `Ultraweak.functionalAbs_spec`;
- `Ultraweak.norm_functionalAbs`;
- `Ultraweak.eq_functionalAbs_of_polar_decomposition`;
- `Ultraweak.functional_polar_decomposition_final_projection`;
- `Ultraweak.existsUnique_functional_polar_decomposition`.

There is no new normal-functional wrapper, support hierarchy, carrier object, decomposition
structure, multiplication notation, or partial-isometry predicate.  Private exposed-face,
large-parameter, support-comparison, and algebraic uniqueness lemmas remain implementation
details.

## Generality decisions

- `PositiveLinearMap.conjugate` is nonunital C-star-algebraic because positivity of conjugation
  needs neither a unit nor a predual.
- Preservation of normality is stated for a specified predual and does not require `WStarAlgebra`.
- Functional support and its conjugation formula require the existing $W^*$ support API.
- The source-facing theorem assumes exactly a $W^*$-algebra with a specified predual, matching
  the mathematical class of the source functional.
- The positive factor is returned as an ordinary positive functional with an explicit normality
  proof, preventing implementation-specific ultraweak wrappers from leaking into downstream API.

## Verification and hygiene

The production module kernel-checks without `sorry`, `admit`, custom axioms, or equivalent
mathematical placeholders.  Principal declarations are proved from Lean, Mathlib, prior LeanOA,
and already integrated Sak-AI infrastructure.  No generated documentation artifact is part of
the mathematical implementation.

```text
CUSTOM AXIOMS ADDED: 0
SORRY/ADMIT ADDED: 0
OTHER MATHEMATICAL PLACEHOLDERS ADDED: 0
```

## Downstream status

The theorem supplies a canonical absolute value for arbitrary normal functionals, exact initial
and final supports, and a discoverable uniqueness eliminator.  These are reusable inputs for
later norm, support, adjoint, and module arguments.  More immediately, this closes the last
numbered theorem in Sakai Section 1.14; the next source frontier is Section 1.15.
