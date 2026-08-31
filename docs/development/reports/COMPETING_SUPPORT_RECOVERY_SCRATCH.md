# Competing-family support-recovery scratch report

Status: kernel-checked theorem-level scratch result; no production API, resolution predicate,
integral, PVM, umbrella import, or Verso change is proposed from this branch

> **Source correction (2026-08-30).** Sakai's clauses use the strong `s(M,M_*)` topology, not
> ultraweak `σ(M,M_*)`. This report's scratch interface is still a valid ultraweak consequence
> after forgetting a same-net strong limit, but it is not itself a source-faithful interface.

## Scope and source

The source is Sakai, Theorem 1.11.3, especially the uniqueness paragraph on printed page 27
(PDF page 39 of `/Users/jonbannon/Desktop/ClaudeMath/SakaiBook_1971.pdf`).  A competing family
`e'` is assumed to satisfy:

1. projection-valuedness and monotonicity;
2. sequential strong-topology continuity from below;
3. endpoint limits `0` and `1` (the display does not repeat the topology);
4. the abstract strong-topology Radon--Stieltjes representation
   `x = integral lambda d e'(lambda)`.

Sakai fixes `lambda_0`, splits the integral for `lambda_0 1 - x` below and above `lambda_0`,
identifies the below integral as the positive part, and then takes support.  His last displayed
line is the strict-left-limit convention

```text
support ((lambda_0 1 - x)^+)
  = integral_{-infinity}^{lambda_0 - 0} d e'
  = e'(lambda_0 - 0)
  = e'(lambda_0).
```

The scratch file is `Scratch/CompetingSupportRecovery.lean`.  It expands the implicit
fixed-projection and order argument without defining an integral.

## Topology-forgotten approximation interface tested

Fix a cut `r`, put `p = e r`, and let `u_i` and `v_i` be finite below-cut and above-cut
translated sums after inserting `r` into each division.  The principal theorem assumes only:

| Hypothesis | Mathematical role | Classification |
| --- | --- | --- |
| `u_i - v_i -> r 1 - a` ultraweakly | translated identity-moment representation | resolution of `a` |
| eventually `0 <= u_i` and `0 <= v_i` | signs of the two split finite sums | derived finite algebra |
| eventually `p * u_i = u_i` | below-cut localization | derived finite projection algebra |
| eventually `p * v_i = 0` | above-cut orthogonality | derived finite projection algebra |
| for every `s < r`, a net `lower_s i -> (r-s) e(s)` ultraweakly | asymptotic lower endpoint removal | endpoint plus linear topology |
| eventually `lower_s i <= u_i` | truncated-affine lower estimate | derived finite order estimate |
| `IsLUB (e '' Iio r) (e r)` | strict-left continuity at the cut | intrinsic family law, derived from Sakai clause 2 |

There is no assumption that `u_i` or `v_i` converges separately.  There is no assumption that a
truncated-affine sum converges to the desired CFC value.  There is no norm convergence, exact
finite endpoint normalization, support continuity, desired support identity, or integral/PVM
object.

The varying lower net is essential.  For Sakai's finite sums the source-correct inequality is

```text
(r-s) * (e(s) - e(left_i)) <= u_i,
```

not `(r-s) * e(s) <= u_i`.  Since only `e(left_i) -> 0` is available, exact finite endpoint
normalization would be a false strengthening.  The generic checked lemma
`tendsto_real_smul_sub_of_tendsto_zero` verifies that these varying lower bounds converge to
`(r-s) * e(s)`.

## Fixed-projection decomposition

`tendsto_split_of_fixedProjection_moment` proves directly from the total moment limit that

```text
u_i -> p * y,
v_i -> p * y - y,
```

where `y = r 1 - a`.  Indeed,

```text
p * (u_i - v_i) = u_i
```

eventually, so separate ultraweak continuity of fixed left multiplication gives the first limit;
subtracting the total limit gives the second.

The ultraweakly closed positive cone then gives

```text
0 <= p*y,
0 <= p*y-y.
```

Projection idempotence and self-adjointness imply that these two limits have zero product.
`CFC.posPart_negPart_unique` therefore identifies them:

```text
y^+ = p*y,
y^- = p*y-y.
```

This is `posPart_negPart_eq_of_fixedProjection_moment`.  It is the decisive noncircular form of
Sakai's implicit positive/negative integral decomposition.  It requires no `WStarAlgebra`; a
C-star algebra with the existing specified-predual and ultraweak order-closed infrastructure is
enough.

## The two support inequalities

`support_spectralPositivePart_le_of_fixedProjection_moment` proves

```text
support (CStarAlgebra.spectralPositivePart a r) <= p.
```

It rewrites `spectralPositivePart` to the Mathlib CFC positive part and uses `p * y^+ = y^+`
with the existing `leftSupport_le_iff` API.

For every `s < r`,
`competing_le_support_spectralPositivePart_of_fixedProjection_moment` passes the varying
inequality `lower_s i <= u_i` through both ultraweak limits.  This gives

```text
(r-s) * e(s) <= y^+.
```

Since `r-s > 0`, the existing support monotonicity machinery yields

```text
e(s) <= support (CStarAlgebra.spectralPositivePart a r).
```

No continuity of support is used.

## Continuity from below and recovery

`isLUB_image_Iio_of_tendsto_below` shows that monotonicity plus any ultraweak approach from
strictly below gives

```text
IsLUB (e '' Set.Iio r) (e r).
```

`isLUB_image_Iio_of_monotone_of_continuousBelow` derives this from Sakai's actual sequential
continuity clause by taking

```text
f(n) = r - 1 / (n+1).
```

Consequently `support_spectralPositivePart_eq_of_fixedProjection_moment` proves the full support
identity, and
`competing_eq_spectralProjectionIio_of_continuousBelow` proves

```text
e(r) = WStarAlgebra.spectralProjectionIio a r.
```

The endpoint is exactly `Iio`: the proof uses all `s < r` and continuity from the left.  An atom
at `r` is excluded.

Pointwise recovery at every real cut gives equality of whole families by
`competing_family_unique_of_pointwise_recovery`.

## What is and is not formalized

Kernel-proved in this lane:

- two-sided ultraweak order-limit passage;
- total-moment-only fixed-projection split;
- CFC positive/negative-part identification;
- the first support inequality;
- every strictly-earlier lower support inequality using varying bounds;
- the `Iio` LUB from Sakai's sequential continuity clause;
- support equality;
- equality with the canonical `spectralProjectionIio`;
- family extensional uniqueness once the pointwise approximation data is available.

Not yet formalized as a source theorem:

- the semantics of Sakai's abstract Radon--Stieltjes representation clause;
- construction, from that clause, of one filtered family of finite divisions whose inserted-cut
  below/above sums satisfy the principal theorem at every `r`;
- the theorem that the representation clause is stable under inserting `r` and `s`;
- endpoint convergence for the selected left endpoints as an instance of clause 3.

The separate source/finite lane has checked the exact compatible finite formulas: its lower bound
is `(r-s) * (e(s)-e(left_i)) <= u_i`, and its below/above sums have the positivity and fixed-
projection identities assumed here.  The remaining gap is therefore the bridge from Sakai's
unformalized abstract integral assertion to these filtered finite approximants.  It is not a new
support-theoretic or CFC obstruction.

## API and architecture assessment

No resolution predicate or structure has earned publication from this lane alone.  The source
representation still lacks a stable Lean meaning, so packaging its assumptions now would merely
hide the remaining semantic choice.

Two theorem-level results deserve integration review:

1. `tendsto_split_of_fixedProjection_moment`;
2. `posPart_negPart_eq_of_fixedProjection_moment`.

They are general, use the established specified-ultraweak topology and Mathlib CFC, and have no
spectral-family dependency.  The first is the small convergence lemma feeding the second.  The
lead should choose their production names and module after comparing the parallel infrastructure
lane; this worker does not publish them.

The support theorem should remain scratch until the finite/source bridge supplies a real consumer
with a stable signature.  A future PVM enters below the theorem stack: its `Iio` restriction and
finite simple-integral approximants should discharge the same monotonicity, localization,
endpoint, lower-bound, and moment hypotheses without altering the CFC target or support proof.

## Validation

Commands run in the isolated worktree
`/private/tmp/sakai-competing-support-73ef4af` on branch
`agent/competing-support-recovery`:

```text
lake build LeanOA.Ultraweak.SpectralProjection
lake env lean Scratch/CompetingSupportRecovery.lean
```

The focused build passed 3,068 jobs.  The final scratch elaboration is warning-free.  The scratch
file contains no `sorry`, `admit`, or added axiom.  No production file, shared coordination file,
Verso source, dependency checkout, remote, or Sak-AI master worktree was changed.
