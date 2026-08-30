# D002 — defer the spectral-integral predicate

Status: Deferred; scratch experiment complete; permanent integral API remains RED

Affected streams: architecture, spectral theorem clusters, Mathlib reconnaissance, Verso

Evidence boundary: Candidate A at local commit `0ee56d4`, Candidate B at local commit `30f266a`,
and the independent comparison at local commit `0bf4f0c`. The prototype files are deliberately
absent from the public `LeanOA` import tree and from Verso.

## Problem

Sak-AI now has spectral bands, arbitrary tagged spectral sums, mesh estimates, norm convergence,
and convergence in every specified ultraweak topology. The next architectural question is whether
that mathematics justifies a stable predicate saying that an operator is a spectral integral.

The experiment compared a topology-generic tagged-partition limit with a predicate specialized to
the existing canonical lower spectral projections. It also tested whether either design can serve
Sakai's uniqueness proof for Theorem 1.11.3, whose integrator is an arbitrary competing resolution
`e'`.

## Candidate A

Candidate A packages cuts, tags, a finite band count, and a declared mesh bound in a
`RealTaggedDivision`. Its `HasTaggedLimit admissible mesh sum x` says that every non-bottom filtered
family of eventually admissible divisions whose mesh tends to zero has sums tending to `x` in an
explicit target topology.

The prototype also constructs the canonical filter

```text
principal {d | admissible d} ⊓ comap mesh (nhds 0)
```

and proves that, once this filter is non-bottom, `HasTaggedLimit` is exactly an ordinary `Tendsto`
statement along it. This is coherent proof-local infrastructure, but it contains no integrator,
refinement, endpoint, additivity, or integrand-regularity semantics. Its algebraic laws merely
restate generic topological convergence laws. No independent Sak-AI consumer justifies making this
vocabulary public.

## Candidate B

Candidate B first defines the finite weighted sum

```text
sum i, f (tag i) • (E (cut (i + 1)) - E (cut i)),
```

where `E r = spectralProjectionIio a r`. Its `HasSpectralIntegral` quantifies over every non-bottom
filtered family of unbundled cuts, tags, band counts, and mesh bounds satisfying the endpoint and
tag conditions, and asks for convergence in the explicitly specified ultraweak topology.

This fits today's tagged-sum API syntactically. Constants telescope, affine combinations are
natural, the identity case directly reuses the landed convergence theorem, and aligned one-band
indicators respect the existing `[r,s)` convention. The predicate is nevertheless hardwired to
the canonical family `spectralProjectionIio a`; it cannot state the competing-resolution clause
needed by Sakai. Parameterizing the finite sum by an arbitrary family is easy, but the limit theory
then needs precisely the unresolved resolution laws.

## Stress-test results

| Test | Candidate A | Candidate B | Finding |
| --- | --- | --- | --- |
| Constants | telescoping plus generic limit | expected `c • 1` limit | both natural |
| Affine combinations | inherited from `Tendsto` | finite and predicate-level laws | no discriminator |
| Aligned steps | finite tagwise formula | correct `[r,s)` one-band formula | finite bands work |
| Steps at atoms | scalar counterexample | spectral counterexample at `a = 0` | unrestricted mesh-only semantics fails |
| Interval restriction | no integral semantics | aligned finite case only | no stable restriction API yet |
| Refinement | dyadic relation exists but predicate ignores it | absent | neither models refinement |
| Uniqueness | requires Hausdorff target and a non-vacuous mesh-zero family | follows from the dyadic witness and Hausdorffness | value uniqueness only |
| Existing lower/upper/tagged sums | identity specialization is definitional | identity specialization is definitional | both reuse the endpoint-tag bridges equally |
| Ultraweak topology | explicit generic target | explicitly fixed to `sigma(M,P)` | topology is not the blocker |
| Arbitrary `e'` | evaluator can vary, but no laws are supplied | impossible in the predicate | decisive source-fidelity failure |

The atom counterexamples are important: a shrinking band carrying a spectral atom may be tagged on
opposite sides of a discontinuous indicator, producing incompatible constant limits. Refinement by
itself does not fix this unless the discontinuity is forced to be a cut with an explicit half-open
convention. Thus neither predicate is a bounded-Borel or simple-function spectral integral.

## Identity-integrand equivalence

The scratch theorem `hasSpectralIntegral_iff_hasTaggedLimit` proves Candidate B equivalent to
Candidate A's canonical spectral specialization for **every** `f : ℝ → ℝ` and proposed `x`, under
the existing $W^*$-algebra and specified-predual assumptions. The requested identity equivalence
is an immediate corollary.

The proof only bundles and unbundles division fields and combines eventual hypotheses. It uses no
spectral estimate. This stronger equivalence is negative design evidence: Candidate B currently
adds a spectral name, not new mathematical semantics.

## Design-contract fit

Publishing A would create a generic permanent wrapper with no demonstrated second consumer.
Publishing B would make a source-critical restriction—the canonical integrator—part of the API.
Either choice would violate the contract's requirements to earn abstractions from recognizable
reusable mathematics and to avoid parallel foundations. Keeping both in scratch space satisfies
the contract and preserves the existing GREEN tagged-sum layer.

## Mathlib fit

Mathlib's `BoxIntegral.HasIntegral` shows that a thin `Tendsto` predicate can be successful when it
sits over a substantial tagged-partition, gauge, basis, and non-vacuity theory. Those semantics are
the reusable structure; Candidate A does not yet possess their spectral analogue.

At audited current-Mathlib commit `2ca39e6`, archived `RiemannStieltjes` is a useful precedent but
not a dependency: it is norm-topological, box-based, absent from the pinned revision, and selects
Riemann mesh semantics. Its box endpoint convention also does not directly encode Sak-AI's
`spectralProjectionIio` band `[r,s)`. `Finpartition` supplies refinement without tags, ordered real
cuts, mesh, or atom ownership; `SimpleFunc` becomes useful only after a set-indexed projection
assignment exists. Original LeanOA contains no competing implementation.

## Downstream implications

The existing public path remains:

```text
spectral bands → tagged sums → mesh estimate → norm limit → specified ultraweak limit.
```

Downstream work should continue to state concrete weighted-sum convergence theorems. It should not
route them through either experimental predicate. A future named integral predicate may be a thin
adapter after its division/filter or arbitrary-resolution semantics have been justified.

## Decision

Choose Outcome 3: both candidates expose a deeper missing abstraction. Publish neither Candidate A
nor Candidate B, and do not add the diagnostic weighted sum merely to support a rejected predicate.
The practical publication decision is therefore deferred.

No public Lean declaration, umbrella import, foundational instance, or Verso node changes in this
transaction.

## Reason

The candidates are formally equivalent well beyond the identity case, so their apparent
difference is presentation rather than structure. Mesh-only arbitrary tagging is provably too
strong for discontinuous integrands at atoms. Most decisively, Sakai's next real consumer varies
the resolution, while Candidate B fixes it and Candidate A supplies none of the laws such a
resolution must satisfy.

The source endpoint is stronger than canonical convergence: from

```text
(lambda_0 1 - x)^+
  = integral_{-infinity}^{lambda_0} (lambda_0 - lambda) d e'(lambda),
```

the support projection must recover `e'(lambda_0)`. A canonical truncated-affine theorem alone
does not complete or faithfully state that uniqueness argument.

The experiment therefore rules out two tempting but premature interfaces and identifies the
source-driven mathematical prerequisite more precisely.

## What remains RED

- a coherent arbitrary lower spectral resolution and its minimum laws;
- a set-indexed projection-valued measure;
- operator-valued spectral integration;
- a bounded-Borel or simple-function calculus, including atom conventions;
- family-independent interval restriction and refinement semantics;
- Sakai's competing-resolution uniqueness theorem.

The specified ultraweak topology and the current canonical finite-sum/convergence theorems do not
become RED; they remain stable inputs.

## Next bounded mathematical step

Prove a tagged **partial-interval norm estimate** for the canonical family, then use it to prove
convergence of aligned weighted sums for

```text
f(lambda) = (lambda_0 - lambda)^+
```

to `CStarAlgebra.spectralPositivePart a lambda_0`. Reuse the existing lower/upper-sum sandwich,
spectral-band telescoping, positive-part identity, and norm-to-ultraweak bridge. Keep the statement
at theorem level and do not introduce a public integral predicate.

After that proof reveals its actual hypotheses, state the analogous target for an arbitrary
competing resolution with those laws explicit. Only then decide whether those laws deserve a
bundled resolution object. Non-aligned partitions and discontinuous step functions remain separate
later problems.

The candidate law list to test—without assuming in advance that all belong in one structure—is:
projection-valuedness and monotonicity; endpoint behavior; the `[r,s)` band convention; band
orthogonality/commutation and finite additivity; the continuity-from-below actually used by the
limit; representation of `x` by the identity weight; and the positive-part/support bridge that
recovers `e'(lambda_0)`.
