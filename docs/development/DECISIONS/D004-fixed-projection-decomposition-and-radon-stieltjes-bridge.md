# D004 — publish fixed-projection decomposition and isolate the Radon--Stieltjes bridge

## Status

Accepted bounded decision. The general fixed-projection ultraweak decomposition and coherent
support helpers are public. Competing-resolution support recovery and Sakai's uniqueness theorem
remain conditional scratch results until the source representation is given refinement-stable
Lean semantics.

Evidence: Sakai/finite audit `6e349da`, fixed-projection audit `c637cb7`, conditional
support-recovery scratch `b25d751`, integrated reports `017eff6`, and consolidated hypothesis
ledger `6b62428`.

## Source boundary

Sakai, Theorem 1.11.3, printed pages 26--27 (PDF pages 38--39), assumes a monotone real-indexed
projection family, sequential ultraweak continuity from below, endpoint limits to zero and one,
and an abstract Radon--Stieltjes representation of the self-adjoint element in the ultraweak
topology. It does not assume exact endpoint projections for each finite division or norm
convergence of moment sums.

The printed uniqueness argument implicitly uses more than one chosen approximating net: it uses
linearity and translation by a constant, insertion of arbitrary cuts, refinement invariance,
positivity, interval splitting, endpoint exhaustion, and the integral of a constant against the
projection increments. The strict convention is `e r = E (Iio r)` and a band is `Ico q s`; an
atom at `r` is excluded from `e r`.

## Public reusable infrastructure

Publish `LeanOA.Ultraweak.ProjectionDecomposition` with:

```text
Ultraweak.tendsto_parts_of_tendsto_sub
Ultraweak.posPart_negPart_eq_of_tendsto_sub_of_isStarProjection
```

The first theorem needs only total specified-ultraweak convergence and the eventual extraction
identity

```text
p * (u i - v i) = u i.
```

It does not require `p` to be a projection, separate convergence assumptions, or a nontrivial
filter. The second adds eventual nonnegativity, a star-projection hypothesis, and the nontrivial
filter needed by ultraweak order closure. Both live at ordered $C^*$-algebra generality, not at the
$W^*$-algebra or spectral-family level.

Also publish the symmetric projection-support simp lemmas and
`WStarAlgebra.le_support_of_smul_le`. The scalar criterion does not need a separate positivity
hypothesis on its self-adjoint upper element: positivity follows from the positive scalar multiple
of the projection and the displayed order inequality.

Do not add ultraweak-named wrappers for fixed left/right multiplication or order-limit passage.
The existing separate-continuity and `OrderClosedTopology` APIs already provide those statements.

## Kernel-checked conditional closure

The finite scratch calculation proves cutoff insertion, band additivity and orthogonality,
below/above localization, positivity, the translated split, and the exact lower estimate

```text
(r - s) • (e s - e left) <= u.
```

The endpoint residual must remain at finite level. Conditional on an inserted-cut total moment net
and the corresponding varying lower nets, the limit scratch proves:

```text
u_i -> e(r) * (r1-a)
v_i -> e(r) * (r1-a) - (r1-a)
(r1-a)^+ = e(r) * (r1-a)
support ((r1-a)^+) = e(r)
e(r) = spectralProjectionIio a r
```

Sakai's sequential continuity clause supplies the required `Iio` least-upper-bound law. Thus no
support-continuity assumption is used, and the complete support and pointwise uniqueness chain is
kernel-checked once the explicit approximation data is supplied.

These conditional spectral theorems remain scratch. Publishing their long hypothesis lists would
freeze the missing representation semantics instead of resolving it.

## Exact remaining blocker

The missing theorem must turn Sakai's abstract ultraweak Radon--Stieltjes representation into a
division-independent directed approximation system and prove that the subsystem containing any
prescribed finite set of cuts remains cofinal and has the same limit. It must also combine the two
endpoint limits with the identity-moment limit to obtain the translated total limit while retaining
the finite left-endpoint residual.

This is a representation/refinement bridge. It is not a missing theorem about fixed
multiplication, ultraweak order closure, positive and negative parts, supports, or Mathlib CFC.

## Public spectral abstraction decision

Do not yet publish `LowerSpectralFamily`, `IsSpectralResolutionOf`, a PVM, or an operator-valued
integral. The unresolved representation semantics is exactly the part such a predicate would need
to express, so packaging current explicit hypotheses would hide rather than solve the design
question.

Mathlib CFC remains the sole continuous functional calculus. The common element is

```text
cfc (fun x : ℝ => (r - x)^+) a.
```

A future PVM can enter below the theorem stack by deriving the `Iio` lower family, finite simple-
integral refinement laws, endpoint limits, and spectral representation. The fixed-projection,
order, support, and CFC conclusions then remain unchanged.

## Next bounded target

Design and kernel-test the smallest division/refinement indexing layer that gives Sakai's abstract
ultraweak Radon--Stieltjes representation a division-independent meaning. Its acceptance test is
cofinal stability under insertion of arbitrary prescribed cuts and derivation of the exact
inserted-cut approximants consumed by the already checked support-recovery proof.
