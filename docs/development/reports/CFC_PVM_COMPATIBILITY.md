# CFC/PVM compatibility report

Status: architecture audit complete; canonical theorem layer accepted; PVM and integral layers
remain deferred

## Evidence boundary

This report records the compatibility conclusion of the truncated-affine transaction.  It is based
on the following kernel-checked and source-audited evidence:

- the canonical production theorem layer at `80bc2d82cab51ecfd96f551c7d0746eb8a18eae3`;
- its named CFC bridge and umbrella integration at `5a2f037`;
- the competing-family scratch result at `de8e2bb`;
- the support/CFC/PVM scratch audit at `f5daad067c64d5d05895a809cbfd7dc3266eb862`;
- pinned Mathlib `476ab284693e554a6b48c5f5210cb4fb5ae51252`;
- current official Mathlib `e62ea4d7200989bad96e0cc05b349c1a5c9800c8`;
- original LeanOA `cb811c1006ae78a0ff1d175253200e1859843370`.

The source endpoint convention was checked against Sakai's proof of Theorem 1.11.3.  The strict
lower half-line is essential: the family is read as `E (Set.Iio r)`, bands are `[r,s)`, and
continuity from below supplies the value at the cut.

The public decision is deliberately narrower than the scratch evidence.  Sak-AI publishes the
canonical theorem layer only.  It does not yet publish a generic lower-family predicate, a PVM, an
operator-valued integral, the generic support criterion, or a competing-resolution theorem.

## 1. What role does Mathlib CFC play in Sak-AI today?

Mathlib's continuous functional calculus is Sak-AI's canonical and only continuous calculus.
Sak-AI uses it for continuous scalar functions of normal or self-adjoint operators and builds the
current spectral layer from those values.  In particular,

```text
CStarAlgebra.spectralPositivePart a r
  = cfc (fun x : ℝ => (r - x)⁺) a.1
  = (algebraMap ℝ M r - a.1)⁺.
```

The first equality is exposed by the non-`simp` theorem
`CStarAlgebra.spectralPositivePart_eq_cfc`; the second is
`CStarAlgebra.spectralPositivePart_eq_posPart`, proved with Mathlib's composition and positive-part
API. Positivity, order comparison, continuous dependence on the scalar cut, and the identification
of finite positive/negative parts remain CFC facts. Sak-AI does not define a competing continuous
calculus.

The production module `LeanOA.Ultraweak.TruncatedSpectralSum` keeps the target visibly equal to this
CFC element.  Its mesh estimate, norm convergence theorem, specified-ultraweak corollary, and dyadic
specialization therefore identify concrete spectral sums with the existing canonical object; they
do not introduce an integral by notation.

## 2. Which current spectral-projection constructions are already derived from or related to CFC?

The dependency is direct:

```text
Mathlib cfc
  -> CStarAlgebra.spectralPositivePart a r
  -> support of that positive element
  -> WStarAlgebra.spectralProjectionIio a r
  -> projection differences, bands, and finite spectral sums.
```

More specifically:

- `WStarAlgebra.spectralProjectionIio a r` is defined as the support of
  `CStarAlgebra.spectralPositivePart a r`.
- `spectralProjectionIio_eq_support_posPart` rewrites that support using the literal translated
  positive part.
- The left/right support identities, `sub_mul_spectralProjectionIio`, monotonicity, band bounds,
  endpoint theorems, and continuity from below are consequences of this construction plus the
  $W^*$-algebra support and order APIs.
- Spectral bands are differences
  `spectralProjectionIio a s - spectralProjectionIio a r`; their intended set convention is
  `Ico r s` because the lower family uses `Iio`.
- Lower, upper, tagged, and truncated-affine sums are finite sums over those bands.
- The support identity
  `support (cfc (fun x => (r - x)^+) a.1) = spectralProjectionIio a r` is definitionally true
  after unfolding the two named wrappers.

These facts form a CFC-to-spectral-projection bridge.  They are not evidence that Mathlib CFC
already contains a PVM or a measurable functional calculus; it does not.

## 3. How should a future PVM layer relate to CFC?

A future PVM should sit below the present theorem layer as set-indexed projection data, not beside
Mathlib as a second continuous calculus.  For the spectral PVM `E_a` of a self-adjoint `a`, its
lower-family view must satisfy

```text
E_a (Set.Iio r) = WStarAlgebra.spectralProjectionIio a r.
```

The PVM laws should derive projection-valuedness, monotonicity, disjoint additivity and
orthogonality, `[r,s)` band identities, continuity from below, and endpoint limits.  A separate
resolution/compatibility theorem should relate the PVM to `a`.  Neither the PVM laws nor the fact
that a particular PVM resolves `a` belongs in `ContinuousFunctionalCalculus`.

This direction preserves the existing public statements: a PVM may later provide new proofs or a
new implementation beneath `spectralProjectionIio`, while the named lower-family and finite-sum
theorems remain the consumer interface.

## 4. What should the compatibility theorem for continuous functions eventually say?

The eventual theorem should say that integration against the spectral PVM of `a` agrees with
Mathlib CFC for every continuous function on the relevant spectrum.  Schematically, and without
committing to a premature integral syntax,

```text
spectralIntegral E_a f = cfc f a.1
```

for the scalar/algebra setting in which `a` is self-adjoint or normal and `f` has the continuity
hypothesis required by Mathlib CFC.  The theorem must also identify the PVM's lower-half-line view
with `spectralProjectionIio`.

The already proved truncated-affine recovery is the first concrete compatibility case:

```text
sum_i (r - tag_i)^+ * (E_a (Iio cut_(i+1)) - E_a (Iio cut_i))
  -> cfc (fun x => (r - x)^+) a.1.
```

The general compatibility theorem should be proved after the PVM and integral semantics exist; it
must not be installed as a field whose only purpose is to make the two calculi agree by assumption.

## 5. Which current theorems should survive unchanged when PVMs are introduced?

The following public theorem families should keep their statements and, where practical, their
names even if their implementations are later refactored through a PVM:

- `CStarAlgebra.spectralPositivePart_eq_cfc`, `spectralPositivePart_eq_posPart`, nonnegativity, and
  cut continuity;
- `spectralProjectionIio_eq_support_posPart` and the left/right support multiplication rules;
- monotonicity, endpoint behavior, continuity from below, commutation, and the
  `spectralProjectionIio_le_iff` universal property;
- canonical band projection, orthogonality, additivity, and spectral-band bounds;
- lower, upper, tagged, and dyadic spectral-sum identities and estimates;
- the production theorems from `LeanOA.Ultraweak.TruncatedSpectralSum`, especially
  `norm_taggedSpectralSum_sub_mul_spectralProjectionIio_sub_le`,
  `spectralPositivePart_mul_spectralProjectionIio_sub_bounds`,
  `norm_truncated_affine_taggedSpectralSum_sub_spectralPositivePart_le`,
  `tendsto_truncated_affine_taggedSpectralSum`,
  `tendsto_truncated_affine_taggedSpectralSum_ultraweak`, and
  `tendsto_truncated_affine_taggedSpectralSum_dyadic`;
- the existing norm-to-specified-ultraweak bridge used by the convergence corollaries.

The finite theorems intentionally mention the current lower-family view.  A future theorem
`E_a (Iio r) = spectralProjectionIio a r` should make them immediately usable from a PVM without
changing their statements.

## 6. Which current declarations are likely temporary adapters?

The local copy of CFC transfer in
`LeanOA.Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Transfer` is a dependency-staging
adapter.  Current Mathlib now has an upstream transfer module with materially the same unital
architecture.  At the next dependency update, Sak-AI should replace the local implementation with
upstream imports or thin compatibility aliases after checking the current nonunital namespace
spelling.

Some local CFC order/norm lemmas in `LeanOA.CFC` now overlap additions in current Mathlib and are
also migration candidates.  Removal should occur only in a focused dependency-update transaction,
because the hypotheses and argument order are not all source-compatible at the audited revisions.

The `toUltraweak_cfc_*` and `ofUltraweak_cfc_*` lemmas are useful Sak-AI-facing rewrite rules.  Their
implementation may become thinner after the transfer migration, but their role need not disappear.
By contrast, `spectralPositivePart`, `spectralProjectionIio`, the band API, and the canonical sum
theorems are semantic names and stable interfaces, not disposable adapters.

The lower-family predicates tested in scratch are not current production declarations and must not
be promoted merely as adapters.

## 7. Are any existing Sak-AI declarations duplicating CFC functionality?

There is no duplicate functional calculus.  `spectralPositivePart` is a thin semantic wrapper
around `cfc`, and its bridge to positive part is useful discoverability rather than parallel
mathematics.  `spectralProjectionIio` adds genuinely $W^*$-algebraic support data absent from CFC.

There are two limited dependency-staging overlaps:

1. Sak-AI's local transfer module predates the corresponding current-Mathlib module.
2. Current Mathlib contains order/norm lemmas overlapping part of `LeanOA.CFC`, including positive-
   and negative-part norm monotonicity and an interval norm bound.

Those overlaps should be retired after a Mathlib bump, subject to signature review.  They do not
justify replacing Sak-AI's spectral projection or truncated-affine theorem layers.

Original LeanOA contains the local CFC/ultraweak transfer staging, but it contains no lower spectral
projection, support-projection spectral layer, PVM, or spectral integral.  The latter parts of
Sak-AI are therefore new rather than duplicates of the read-only upstream repository.

## 8. Does the proposed lower-family design preserve Mathlib's avoidance of problematic term-dependent typeclass architecture?

Yes, provided the deferred design remains explicit data plus ordinary hypotheses or a bundled
structure passed as a term.  It must not become a typeclass such as an inferred
`[SpectralResolutionOf a e]`, whose instance search depends on particular operator and family
terms.

The scratch theorem deliberately accepted
`e : ℝ → {p // IsStarProjection p}` and explicit monotonicity, endpoint, cut, and convergence
hypotheses.  That exposed which facts were intrinsic to `e` and which related `e` to `a`.  A future
PVM may bundle set-indexed projection laws as mathematical data, while a relation saying that it
resolves `a` should remain an explicit proposition/argument.  Mathlib's type-level CFC class stays
unchanged.

No lower-family abstraction is published by this decision, so the current production API already
satisfies this constraint.

## 9. How should CFC transfer interact with Sak-AI's ultraweak topology infrastructure?

CFC construction and ultraweak convergence have distinct jobs:

- Transfer equips the ultraweak type synonym with the same algebraic CFC through the continuous
  star-algebra equivalence from the normed presentation and proves value-identification rewrites.
- It does not assert that positive part or `a |-> cfc f a` is ultraweakly continuous.
- Norm convergence of spectral sums may be transported to the specified ultraweak topology with
  `continuous_toUltraweak`, as the current canonical theorem does.
- An argument whose input is only ultraweak convergence cannot be sent through
  `Filter.Tendsto.cfc`.  It needs separate $W^*$-algebraic facts, such as ultraweak closedness of
  positivity and separate ultraweak continuity of multiplication by a fixed element.

After a Mathlib update, the upstream transfer module should replace Sak-AI's local staging, while
the `toUltraweak_cfc_*` and `ofUltraweak_cfc_*` rewrite interface may remain.  This migration must
not conflate equality of CFC values across type synonyms with convergence of approximants.

## 10. What should remain explicitly outside the CFC class itself?

The following belong outside `ContinuousFunctionalCalculus`:

- supports and $W^*$-algebra projection-lattice operations;
- lower spectral families, set-indexed PVMs, and their endpoint/continuity laws;
- Borel or measurable functional calculus;
- operator-valued spectral integration and its convergence mode;
- the relation asserting that a PVM or lower family resolves a particular operator;
- ultraweak representation theorems, convergence of spectral sums, and topology bridges;
- support-recovery criteria and competing-resolution uniqueness;
- atom ownership and the `Iio`/`Ico` endpoint convention;
- refinement, division, and tagged-sum infrastructure.

Mathlib CFC should continue to provide continuous-function evaluation, composition, spectral
mapping, positivity/order consequences, and uniqueness in its native continuous setting.  The PVM
layer should consume that calculus through proved compatibility theorems rather than enlarge the
CFC class with $W^*$-specific or term-dependent fields.

## Scratch conclusions that are not public API

The competing-family experiment proves a useful finite algebraic fact: for a monotone
projection-valued family with exact finite endpoints, the truncated-affine weighted sum is the
positive part of the corresponding affine identity-weighted step operator.  Norm convergence of
those step operators then yields convergence to the same CFC target. This is strong compatibility
evidence, but its exact endpoints and norm convergence are stronger than Sakai's strong-topology
source hypotheses and do not settle his undefined integral semantics.

The support experiment proves a topology-free sufficient criterion: the target is fixed by `e r`,
each `e s` for `s < r` is dominated by the support through a strictly positive scalar lower bound,
and `e r` is the least upper bound of the earlier projections.  It also proves that support is not
norm-continuous at zero.  Thus convergence alone cannot recover the family at the endpoint.

Both results remain scratch evidence.  The generic finite-family theorem, the lower-family
predicates, and the generic support criterion are deferred until a source-faithful competing
resolution or a second genuine consumer determines their stable signatures.

## Architectural conclusion

The compatible architecture is:

```text
Mathlib continuous functional calculus (canonical)
  -> Sak-AI CFC-named continuous targets
  -> current support-defined Iio spectral projections
  -> canonical band and finite-sum theorem layer

future PVM and spectral integral
  -> derive Iio/Ico family laws below that theorem layer
  -> prove continuous-function compatibility with Mathlib cfc
  -> recover the same current public theorems
  -> support source-faithful competing-resolution uniqueness.
```

Only the upper canonical chain is public now.  The lower future chain remains an explicitly RED
boundary.
