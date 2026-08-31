# Sakai polar regularizer report

## Scope and source

This report covers only WS-3, the proof-local regularizer in Sakai, Theorem 1.12.1.  The source is
Sakai, *C*-Algebras and *W*-Algebras, printed pp. 27--28 (local PDF pp. 39--40).

Sakai indexes by positive integers and defines

```text
h(n) = (a* a + (1/n) 1)^(1/2),
a(n) = a (a* a + (1/n) 1)^(-1/2).
```

He then writes the conjugated product for `a(n)* a(n)`, concludes `‖a(n)‖ <= 1`, proves
`a(n) h(n) = a`, and states that `h(n) -> (a* a)^(1/2)` uniformly.  Here “uniformly” is the
C*-algebra norm convergence furnished by continuous functional calculus.  On printed p. 28 the
source next invokes “the weak compactness of the unit sphere `S` of `M`” to obtain an accumulation
point.  In context `S` is the closed unit ball: the preceding estimate is `<= 1`, and the later
notation `a + epsilon S` also uses the closed unit ball.

The phrase “weak compactness” cannot mean Banach-space weak compactness in general.  For a
W*-algebra regarded as the dual of its predual, the source-faithful formal realization is weak-star,
that is Sak-AI's specified ultraweak topology `sigma(M,P)`.  This is also the topology recorded in
the section scope audit.  The literal source phrase and this formal interpretation should both be
retained in downstream documentation.

## Checked CFC realization

The scratch implementation is
`Scratch/SakaiElementPolarRegularizer.lean`.  It uses pinned Mathlib's canonical `CFC.sqrt`, real
`CFC.rpow`, and `CFC.abs`; it introduces no alternative calculus and imports no in-flight WS-1
declaration.  Sakai's positive-integer sequence is reindexed over Lean naturals exactly as

```text
epsilon n = ((n + 1 : Real)^-1)
c a n     = star a * a + epsilon n • 1
h a n     = CFC.sqrt (c a n)
aReg a n  = a * (c a n) ^ (-(1 / 2 : Real)).
```

The file kernel-proves:

- `epsilon_pos` and `epsilon_tendsto_zero`;
- `c_nonneg` and `c_strictlyPositive`;
- `star_aReg_mul_aReg`, the exact noncommutative identity

  ```text
  star (aReg a n) * aReg a n
    = c a n ^ (-1/2) * (star a * a) * c a n ^ (-1/2);
  ```

- `norm_aReg_le_one` and the compactness-ready form `aReg_mem_unitClosedBall`;
- `aReg_mul_h : aReg a n * h a n = a`;
- `c_tendsto_star_mul_self` in norm;
- `h_tendsto_abs : h a -> CFC.abs a` in norm;
- `aReg_mul_abs_tendsto : aReg a n * CFC.abs a -> a` in norm.

The contraction estimate uses Mathlib's order theorem `le_iff_norm_sqrt_mul_rpow`, after proving
`star a * a <= c a n`.  Equality of the two relevant norms is obtained from the C*-identity and
the checked conjugated product.  No informal division in a noncommutative algebra is used.  The
optional rewrite through `Ring.inverse (c a n)` was not needed by a consumer and was deliberately
not added.

The final convergence is a direct consequence of

```text
aReg n * CFC.abs a - a = aReg n * (CFC.abs a - h n)
```

together with `‖aReg n‖ <= 1`.  It is therefore norm convergence, stronger than the ultraweak
convergence needed after compactness, without changing the source theorem.

## Compactness audit and handoff

The compactness infrastructure already exists; WS-4 should reuse it rather than add a new
Banach--Alaoglu layer.

- `LeanOA/Ultraweak/Basic.lean` provides `Ultraweak.isCompact_closedBall`.  For a specified predual
  `P`, it proves compactness of

  ```text
  ofUltraweak ⁻¹' Metric.closedBall (0 : M) 1 : Set sigma(M,P)
  ```

  by transport from Mathlib's `WeakDual.isCompact_closedBall`.
- Mathlib provides `IsCompact.exists_mapClusterPt`.  This is the appropriate interface for the
  `Nat`-sequence; a subsequence must not be used because the ultraweak topology is not known to be
  first countable.
- `aReg_mem_unitClosedBall` supplies the pointwise membership needed to show that the mapped
  `atTop` filter is carried by the compact set.
- `LeanOA/Ultraweak/Multiplication.lean` provides `Ultraweak.continuous_mulRightₗ` and the bundled
  `Ultraweak.mulRightL`.  Thus a cluster point `b` of `aReg a` is sent to a cluster point of
  `aReg a n * CFC.abs a` by fixed right multiplication.  The checked norm convergence, followed by
  `continuous_toUltraweak` and Hausdorff uniqueness of the cluster value, yields
  `b * CFC.abs a = a`.

The compactness theorem itself requires a normed specified predual
`[NormedAddCommGroup P] [NormedSpace Complex P] [Predual Complex M P]`.  The currently available
separate-multiplication bridge additionally assumes `[CompleteSpace P]`.  This completeness is
standard in Sak-AI's W*-algebra development and is an infrastructure signature requirement, not a
new mathematical assumption on Sakai's theorem.

An exact downstream filter shape is therefore:

```text
u n = toUltraweak Complex P (aReg a n)
K   = ofUltraweak ⁻¹' Metric.closedBall (0 : M) 1

Ultraweak.isCompact_closedBall ...
  + (forall n, u n in K)
  -> exists bSigma in K, MapClusterPt bSigma atTop u.
```

Set `b = ofUltraweak bSigma`.  Fixed-right-multiplication continuity and
`aReg_mul_abs_tendsto` then give `b * CFC.abs a = a`, while membership in `K` gives `‖b‖ <= 1`.
This extraction and limit passage are routine local engineering, not missing Mathlib machinery.

## Required support facts and exact remaining existence proof

The regularizer stream itself needs no support theorem.  After obtaining `b`, WS-4 still needs the
independent support layer to carry out Sakai's cutdown.  With

```text
p = support (CFC.abs a),
q = support (CFC.abs (star a)),
u = q * b * p
```

(or the reviewed equivalent simplification), it must prove that `u` is a partial isometry with

```text
star u * u = p,
u * star u = q,
a = u * CFC.abs a.
```

Those are WS-2/WS-4 obligations.  In particular WS-4 must not infer joint ultraweak continuity of
multiplication; only multiplication by the fixed element `CFC.abs a` is used in the cluster-point
passage.  Once the cutdown and the two support equations are proved, uniqueness and the exact
Theorem 1.12.1 package remain downstream.

## Fidelity and status

The route is **source-faithful for the regularization stage**:

- the only indexing change is the explicit bijective reindexing `n >= 1` to `n : Nat` by `n + 1`;
- the CFC definitions are Sakai's exact functions;
- the product statement is made more precise, not altered, by avoiding commutative quotient
  notation;
- all convergence in this module is norm convergence, matching the source's “uniformly” step;
- the compactness handoff is recorded as ultraweak/weak-star and not confused with the strong
  topology of the preceding section.

Validation performed:

```text
lake env lean Scratch/SakaiElementPolarRegularizer.lean
```

It succeeds with no errors or warnings.  A `#print axioms` audit of the five principal theorems
reports only Lean's standard `propext`, `Classical.choice`, and `Quot.sound` dependencies.

```text
CUSTOM AXIOMS ADDED: 0
SORRY/ADMIT ADDED: 0
OTHER PLACEHOLDERS ADDED: 0
```

Status: **WS-3 GREEN in scratch**.  Production must not import this file.  After integration review,
WS-4 should transplant the proof-local definitions and proofs privately, or promote only a helper
with an independently reusable signature.
