# Sakai 1.14.4: general functional polar-decomposition source audit

## Status and source

This report records the direct source audit for Sakai, Theorem 1.14.4.  The production
implementation is documented separately in
`SAKAI_1_14_4_FUNCTIONAL_POLAR_DECOMPOSITION.md`.

Source: Sakai, *$C^*$-Algebras and $W^*$-Algebras*, Section 1.14, printed pp. 32--33
(local `SakaiBook_1971.pdf`, PDF pp. 44--45).  The immediately preceding Section 1.14
material was checked on printed p. 31 (PDF p. 43) to fix the support notation.  The pages were
read directly from the scan; the statement below is not reconstructed from a secondary source.

Section 1.14 ends after the historical note following this theorem.  Section 1.15 begins on
printed p. 33 (PDF p. 45); there is no further numbered Section 1.14 result.

## Exact source statement

Let `M` be a $W^*$-algebra and let `g` be an arbitrary ultraweakly continuous complex linear
functional on `M`.  Sakai proves that `g` has a unique polar decomposition

```text
g = R_v phi,
```

where:

- `phi` is a normal positive linear functional;
- `v` is a partial isometry;
- `‖g‖ = ‖phi‖`;
- the initial projection is

  ```text
  v* v = s(phi);
  ```

- the final projection is

  ```text
  v v* = s(|g*|).
  ```

The uniqueness is uniqueness of the normalized decomposition, hence of the pair `(v, phi)`, not
merely uniqueness of the positive factor.  Sakai subsequently writes the unique positive factor
as `|g|`.

There is no assumption that `g` is nonzero, self-adjoint, normalized, a state, faithful, or
defined on a factor.  There are no separability or sigma-finiteness hypotheses.

## Multiplication convention

The right-action convention is load-bearing.  Sakai's notation is

```text
(R_u g)(x) = g(x u).
```

Consequently the theorem's displayed identity means

```text
(R_v phi)(x) = phi(x v),
```

and not `phi(v x)`.  The production translation uses the established
`PositiveLinearMap.cutoff` operation, whose application law is exactly

```text
phi.cutoff v x = phi (x * v).
```

No star or opposite-action conversion is hidden in the source-facing factorization.

## Support orientation

The support in `v* v = s(phi)` is Definition 1.14.2's support of the normal positive
functional.  It is the **initial** projection of `v`.  The final projection is `v v*` and is the
support of the positive factor belonging to the adjoint functional, namely `|g*|`.

The source does not define a support projection of the arbitrary functional `g` itself.  Thus the
formalization should not introduce a second support operation for general linear functionals.
It should use `PositiveLinearMap.support` for `|g|` and `|g*|`.

## Proof structure in the source

The source proof exposes the following architecture.

1. Work with an exposed face of the unit ball on which the real part of `g` attains its norm,
   and choose an extreme point `u` of that face.
2. The right translate `R_u g` is positive and has the same norm as `g`.
3. Use the carrier/support of this positive functional to trim the extreme multiplier: the proof
   forms the support-normalized partial isometry from `u` and `s(R_u g)`.
4. Obtain the exact right factorization and the initial-support equality.
5. Compare two normalized factorizations, use support cutdown and the null-ideal criterion, and
   deduce uniqueness of both the multiplier and the positive functional.
6. Apply the same construction to `g*` to identify the final projection with `s(|g*|)`.

This proof is a general-functional analogue of the exposed-face argument already used in
`Ultraweak.PolarDecomposition`, but it is not a corollary of that file's public theorem: the old
public result restricts to self-adjoint functionals and produces a self-adjoint unitary acting on
the left.

## Source-fidelity checklist

| Source datum | Certified translation |
| --- | --- |
| functional class | arbitrary `g : sigma(M,P) ->L[ℂ] ℂ` |
| positive factor | ordinary `M ->p[ℂ] ℂ` with explicit normality |
| action | right action, `g(x) = phi(x * v)` |
| norm | `‖g‖ = ‖phi‖` on the underlying algebra |
| initial projection | `star v * v = support phi` |
| final projection | `v * star v = support (functionalAbs g*)` |
| partial isometry | represented by the initial-projection equation |
| uniqueness | unique pair `(v, phi)` under the displayed normalizations |
| absolute value | the unique positive factor, published only after uniqueness |

No source hypothesis was strengthened in the production statement, and no displayed conclusion
was dropped.  In particular, the final-projection clause is part of the exact source-facing
theorem rather than an untracked comment.

## Relationship to adjacent Section 1.14 results

Definition 1.14.2 supplies the functional support, its greatest-zero-projection theorem, and its
cutdown/null-ideal API.  These are used in the support trimming and uniqueness arguments.
Theorem 1.14.3 supplies the orthogonal Jordan decomposition of a self-adjoint functional, but it
is not used as an artificial route to the general theorem.  The direct exposed-face route is both
closer to Sakai's proof and better aligned with the existing analytic factorization engine.

With Theorem 1.14.4 completed, every numbered item in Section 1.14 is source-formalized.
