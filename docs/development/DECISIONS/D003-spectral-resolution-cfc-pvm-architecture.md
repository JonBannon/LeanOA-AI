# D003 — keep Mathlib CFC canonical and defer the PVM layer

## Status

Accepted bounded decision; canonical theorem layer is public, lower-family/PVM/integral
architecture remains RED.

Evidence: canonical production module at `80bc2d82cab51ecfd96f551c7d0746eb8a18eae3`,
named CFC bridge and umbrella integration at `5a2f037`,
competing-family scratch result at `de8e2bb`, and support/CFC/PVM audit at
`f5daad067c64d5d05895a809cbfd7dc3266eb862`.

**Source correction (2026-08-30).** Sakai's printed continuity and abstract-integral topology is
`s(M,M_*)`, not `σ(M,M_*)`. References below to ultraweak convergence describe the still-valid
modern consequence used by the conditional support proof, not the literal source hypothesis.

## Canonical truncated-affine theorem

Publish the theorem-only module `LeanOA.Ultraweak.TruncatedSpectralSum`.  Its target is the existing
Mathlib-CFC element

```text
CStarAlgebra.spectralPositivePart a r = cfc (fun x : ℝ => (r - x)⁺) a.1.
```

The public layer includes the partial-interval estimate, canonical band bounds, endpoint
sandwiches, the sharp mesh estimate, filter-general norm convergence, specified-ultraweak
convergence, and dyadic convergence.  The cutoff need not be a partition point.  No spectral
integral or resolution structure is introduced.

## Mathlib CFC relationship

Mathlib CFC remains Sak-AI's canonical and only continuous functional calculus.
`CStarAlgebra.spectralPositivePart` is a semantic wrapper around `cfc`, and
`spectralPositivePart_eq_cfc` and `spectralPositivePart_eq_posPart` are the named bridges to the
generic CFC value and literal translated positive part. A future PVM/integral API must prove
agreement with CFC on continuous functions; it must not create a second continuous calculus or add
PVM fields to the CFC class.

The local CFC transfer staging may be replaced by current Mathlib's transfer module at a future
dependency update.  That is a compatibility migration, not an architectural change.

## Minimal lower-family assumptions

The scratch evidence separates three levels:

- projection-valuedness and monotonicity suffice for the finite band projection, orthogonality,
  positivity, and truncated-affine positive/negative decomposition;
- the exact finite telescoping theorem additionally assumes endpoint values `0` and `1` for the
  chosen cuts;
- endpoint support recovery additionally needs continuity from below, expressed order-theoretically
  as `e r` being the least upper bound of `e s` for `s < r`.

These are evidence about future signatures, not an accepted public structure.  In particular,
neither the scratch `IsIntrinsicLowerFamily` predicate nor any bundled lower-family type is
published.  Any future relation between a family and an operator must be an explicit term-level
argument, not a term-dependent typeclass.

## Resolution-of-a assumptions

The relation between a lower family `e` and an operator `a` is separate from intrinsic family laws.
The competing-family scratch theorem uses norm convergence of identity-weighted step operators to
`a` together with exact finite endpoints.  Those hypotheses are sufficient for its CFC argument
but are stronger than Sakai's source assumptions and are not accepted as the definition of a
resolution.

A source-faithful relation would have to encode Sakai's strong-topology Radon--Stieltjes
representation of `a` independently of one privileged sequence of divisions. It must be stable
under insertion of an arbitrary cut and strong enough to derive the positive/negative decomposition
needed for support recovery.  It must not assume the desired truncated-affine limit or support
identity.

## Future PVM-derived assumptions

For a future PVM `E`, define the lower-family view by

```text
e r = E (Set.Iio r).
```

The PVM layer should derive:

- projection-valuedness;
- monotonicity under inclusion;
- `Iio s \ Iio r = Ico r s` band semantics for `r <= s`;
- disjoint-band orthogonality and additivity;
- continuity from below;
- limits to `0` and `1` at the two infinities.

These are properties of the family.  A further theorem must state that the PVM resolves `a` and
must prove continuous-function compatibility with Mathlib CFC.

## Support-recovery status

For the canonical family, support recovery is already exact: support of
`cfc (fun x => (r - x)^+) a.1` is definitionally `spectralProjectionIio a r` after unfolding the
named wrappers.

For an arbitrary competing family, recovery is not proved.  Scratch code kernel-checks a generic
order criterion using an upper-support identity, strictly positive lower bounds for every earlier
projection, and a least-upper-bound hypothesis.  It also proves that support is not norm-continuous
at zero, so neither norm nor ultraweak convergence alone permits passage to support.

The generic criterion is not published by this decision.  It may be reconsidered after a
source-faithful competing-family proof or a second genuine consumer fixes its useful signature.

The endpoint convention is fixed: `e r = E (Iio r)`, bands are `Ico r s`, and an atom exactly at
`r` is excluded.  The scalar atom test at zero is kernel-checked.

## Competing-resolution uniqueness

Sakai's arbitrary competing-resolution uniqueness theorem is not proved and remains RED. The
finite scratch identity and its norm-limit corollary do not close the source theorem because Sakai
uses strong-topology continuity and representation with asymptotic endpoints, not exact endpoints
and norm convergence; moreover, his integral's division semantics are undefined.
The family can also be unconstrained at an unsampled cut unless approximation is stable under cut
insertion and continuity from below is used.

No theorem may be described as the source uniqueness result until the hypotheses and both the
support-recovery and pointwise-family conclusions have been checked against Sakai.

## Continuous-function compatibility strategy

The eventual compatibility theorem should have the mathematical content

```text
spectralIntegral E_a f = cfc f a.1
```

for continuous `f` on the relevant spectrum, together with
`E_a (Iio r) = spectralProjectionIio a r`.  The truncated-affine convergence theorem is the first
concrete instance and fixes the CFC target without needing an integral object.

The compatibility theorem should be derived from a coherent PVM/integral construction.  It must not
be a field added merely to force agreement.  Borel or measurable extensions remain a separate
later layer.

## CFC transfer / ultraweak interaction

CFC transfer identifies the algebraic CFC value in the normed algebra and its ultraweak type
synonym.  It does not make positive part or operator-variable CFC ultraweakly continuous.

Consequently:

- norm convergence may be sent to the specified ultraweak topology through
  `continuous_toUltraweak`;
- an ultraweak-only approximation cannot be passed through `Filter.Tendsto.cfc`;
- source-faithful competing-resolution work must instead use $W^*$-specific facts such as
  ultraweak closedness of positivity and separate ultraweak continuity of multiplication by a
  fixed projection.

On a future Mathlib bump, migrate the local transfer implementation to upstream without changing
this separation of responsibilities.

## Public API decision

Publish only the canonical theorem layer at `80bc2d8`, its named CFC bridge, and its umbrella import
at `5a2f037`.

Defer all of the following:

- a lower-family structure or predicate;
- a resolution-of-an-operator structure or predicate;
- a set-indexed PVM;
- an operator-valued spectral integral;
- the competing-family finite theorem;
- the generic support-recovery criterion;
- arbitrary competing-resolution uniqueness.

Scratch evidence remains available in its isolated revisions and reports.  It does not enter the
`LeanOA` import tree or Verso.

## Remaining RED boundaries

- coherent set-indexed projection-valued measures;
- operator-valued spectral integration;
- bounded-Borel/measurable functional calculus and atom conventions beyond the fixed `Iio`/`Ico`
  family convention;
- a source-faithful, division-independent relation saying that an arbitrary family resolves `a`;
- ultraweak positive/negative decomposition for arbitrary competing families;
- support recovery and pointwise uniqueness for a competing resolution;
- general continuous-function PVM/CFC compatibility;
- family-independent interval restriction and refinement semantics.

The current support-defined canonical family, band calculus, finite sums, mesh estimates, norm
convergence, and specified-ultraweak corollaries remain GREEN.

## Future PVM migration strategy

1. Introduce a PVM only after its first source-faithful consumers determine the minimal set-indexed
   interface.
2. Define its lower-half-line view using `Iio` and derive the current monotonicity, band,
   orthogonality, endpoint, and continuity-from-below laws.
3. Construct the PVM associated to a self-adjoint operator and prove
   `E_a (Iio r) = spectralProjectionIio a r`.
4. Define spectral integration and prove agreement with Mathlib CFC for continuous functions.
5. Reuse the existing public band and sum theorem layer through the half-line equality; do not fork
   it into PVM-specific duplicates.
6. Only after the compatibility theorem is established, extend toward simple/Borel functions and
   migrate proofs whose natural home is the PVM layer.

## Next bounded target

Scratch-test Sakai's fixed-projection ultraweak decomposition argument for an arbitrary competing
family under his actual hypotheses.  The transaction should make arbitrary insertion of the cutoff
explicit, derive the below-cut positive part and above-cut negative part using ultraweakly closed
order and fixed-projection multiplication, and determine whether those results supply the upper
support identity and strict lower bounds required for recovery.

Keep every family and resolution hypothesis explicit.  Do not introduce a public structure, PVM,
integral, or generic support theorem during that test.
