# Sakai Section 1.14 scope

## Boundary and source

Source: Sakai, *$C^*$-Algebras and $W^*$-Algebras*, Section 1.14, printed
pp. 31--33 (local PDF pp. 43--45) in
`/Users/jonbannon/Desktop/ClaudeMath/SakaiBook_1971.pdf`.

Section 1.14 is **Polar Decomposition of Linear Functionals on a $W^*$-Algebra**.  It ends before
Section 1.15, **Concrete $C^*$-Algebras and $W^*$-Algebras**, on printed p. 33.

This document is a bounded scope audit only.  It does not mark any result of Section 1.14 as
source-formalized.

## Numbered source inventory

| Item | Printed / PDF page | Source content |
| --- | --- | --- |
| Definition 1.14.1 | 31 / 43 | Positive functionals `φ₁` and `φ₂` are orthogonal when `‖φ₁ - φ₂‖ = ‖φ₁‖ + ‖φ₂‖`. |
| Definition 1.14.2 | 31 / 43 | For a normal positive functional `φ`, the left ideal `L = {x | φ(x* x) = 0}` is strongly, hence ultraweakly, closed and is `M p`.  Its complementary projection is the support `s(φ)`.  The source records greatest-zero-projection, cutdown, faithfulness, and faithful-family consequences. |
| Theorem 1.14.3 | 31--32 / 43--44 | A self-adjoint predual functional has a unique difference `f = f⁺ - f⁻` of orthogonal normal positive functionals with `‖f‖ = ‖f⁺‖ + ‖f⁻‖`. |
| Theorem 1.14.4 | 32--33 / 44--45 | Every ultraweakly continuous functional has a unique polar decomposition `g = R_v φ`, where `φ` is normal positive, `‖g‖ = ‖φ‖`, and `v` is a partial isometry with initial projection `s(φ)`; the source also identifies its final projection. |

## Source dependency order

The useful dependency order is not simply the printed order:

```text
normal positive functional + Cauchy--Schwarz
  -> null left ideal Lφ
  -> ultraweakly closed principal left ideal
  -> support projection s(φ) and cutdown identities
  -> faithfulness and support comparison
  -> uniqueness machinery for positive decompositions

orthogonality of positive functionals
  -> self-adjoint Jordan decomposition (1.14.3)
  -> general functional polar decomposition (1.14.4)
```

The support projection is therefore the natural first bounded checkpoint.

## Existing Sak-AI coverage

The section does not start from zero.

- `PositiveLinearMap.isNormalOnProjections_iff_mem_continuousDual` and the Section 1.13 order
  characterizations already identify normal positive functionals without adding another normality
  object.
- `Ultraweak.Ideal` identifies ultraweakly closed left ideals with projection-generated ideals.
- `PositiveLinearMap.cauchy_schwarz_star_mul` and the surrounding positive-functional API provide
  the null-space estimates needed to prove that `Lφ` is a left ideal.
- `Ultraweak.Multiplication`, `Ultraweak.Corner`, and the projection lattice provide the expected
  cutdown and support environment.
- `Ultraweak.PolarDecomposition` already proves that a self-adjoint ultraweakly continuous
  functional factors through left multiplication by a self-adjoint unitary and a positive
  ultraweakly continuous functional.  This is relevant input to 1.14.3, but it is not yet Sakai's
  orthogonal positive/negative decomposition.
- `Ultraweak.ElementPolarDecomposition` concerns algebra elements, not linear functionals.  It
  must not be confused with Theorem 1.14.4.
- `IsStarProjection`, the existing support projections of algebra elements, and the established
  partial-isometry equations should be reused rather than replaced by a local predicate.

## External-library audit

Pinned Mathlib, audited current Mathlib at
`567908cf509fb0bab796e5401edf35b4492ae48f`, original LeanOA at
`cb811c1006ae78a0ff1d175253200e1859843370`, and the current Sak-AI tree were searched for a
support projection of a positive functional, orthogonality/Jordan decomposition of positive
functionals, and polar decomposition of normal functionals.  No directly reusable complete API
was found.

Mathlib does supply the generic positive-linear-map, continuous-dual, convexity, extreme-point,
unitary, and partial-isometry ingredients.  Sak-AI should continue to use those canonical objects.
The missing layer is operator-algebraic assembly, not a new functional or projection foundation.

## Missing infrastructure

### First checkpoint: support of a normal positive functional

The next transaction should seek a theorem-level support API with no new normality notion:

1. define the null left ideal using the canonical positive functional;
2. prove it is ultraweakly closed, preferably by reusing normality/predual continuity rather than
   introducing a second topology-specific closure object;
3. obtain its generating projection from the existing ideal theorem;
4. define the complementary support projection only after uniqueness makes the choice canonical;
5. prove the greatest-zero-projection characterization;
6. prove `φ(x) = φ(s(φ)x) = φ(xs(φ)) = φ(s(φ)xs(φ))`;
7. relate full support to faithfulness.

The source first mentions strong closedness and then invokes 1.8.11 to get ultraweak closedness.
A Lean proof may go directly through ultraweak continuity if it proves the same mathematical
claim with weaker infrastructure; the report for that transaction must record the deviation.

### Later clusters

| Cluster | Dependencies | Parallel safety |
| --- | --- | --- |
| Functional orthogonality API (1.14.1) | normed positive functionals only | Safe reconnaissance; publish only if consumed by 1.14.3. |
| Support/faithfulness (1.14.2) | Section 1.13 normality, ideals, cutdowns | Foundational owner; should land first. |
| Orthogonal Jordan decomposition (1.14.3) | orthogonality + support; existing self-adjoint-unitary factorization may shorten existence | Begins after support signatures stabilize. |
| General polar decomposition (1.14.4) | support + partial isometries + normal functional multiplication; likely uses extreme points | Begins after support and 1.14.3 API review. |

## Design constraints for the next wave

- Keep `PositiveLinearMap.IsNormalOnProjections` and specified-predual membership as the settled
  normality vocabulary.
- Do not reuse the algebra-element `support` name without a namespace/type distinction that makes
  functional support unambiguous.
- Do not add a broad partial-isometry structure solely for this theorem; use the established
  projection equations unless a reusable structure already exists upstream.
- Preserve Sakai's left/right multiplication orientation explicitly in the polar-decomposition
  statement.
- Separate existence, uniqueness, support identities, and norm identities into discoverable
  lemmas before packaging an exact source theorem.
- Re-audit the exact meaning of `R_v φ` before fixing the public theorem signature.

## Recommended next bounded transaction

```text
Sakai 1.14.2: normal-positive-functional support projection
```

Success should mean that the null ideal, canonical support projection, greatest-zero-projection
property, cutdown identities, and faithfulness criterion are all kernel-proved and documented.
It should not automatically launch the full polar-decomposition theorem in the same transaction.
