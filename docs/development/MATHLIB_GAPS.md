# Mathlib overlap and gap log

This is an API-reconnaissance log, not a commitment to upstream every helper.

## Already exists — reuse it

- Mathlib's native `TwoSidedIdeal` is the accepted Sak-AI representation.
- `IsStarProjection.le_iff_sub` supplies projection differences from order; do not re-prove the
  general result in Sak-AI.
- Mathlib's continuous functional calculus, self-adjoint subtype, and GNS construction are the
  foundations for the current C*-algebra and representation work.
- Standard filters, finite sums, and normed-space integration should be reused wherever their
  codomain assumptions fit; the spectral audit must determine where they stop fitting.

## Local helpers / plausible upstream candidates

- `IsStarProjection.mul_eq_self_of_nonneg_of_le_of_mul_eq_self` is a general hereditary-support
  lemma already isolated in the mirrored Mathlib hierarchy.
- The semiring-level annihilator lemmas may be upstreamable independently of the unresolved
  `TwoSidedIdeal` representation question.
- Generic weak-bilinear transport and compatibility lemmas should be compared to current Mathlib
  before further local expansion.
- Current Mathlib master contains `IsSelfAdjoint.norm_le_max_of_le_of_le`, but it is not an exact
  drop-in replacement for the pinned local declaration in `LeanOA/CFC.lean`: upstream assumes the
  middle element is self-adjoint, while the local signature derives that fact from a self-adjoint
  lower bound. On the next Mathlib update, remove the local duplicate and make the middle
  self-adjointness explicit at consumers such as tagged spectral sums.

## Major infrastructure question

- No accepted local set-indexed projection-valued-measure or operator-valued integration interface
  has been identified. Audit pinned and current Mathlib before introducing one. A scalar/vector
  Bochner integral is not automatically the right codomain for W*-algebra-valued spectral
  integration.

The completed audit in `reports/MATHLIB_SPECTRAL_AUDIT.md` distinguishes the implementation layers
precisely (its original identification of Sakai's topology has since been corrected):
`VectorMeasure` can express topology-parametric additivity, but its integral uses norm variation;
current `Archive/RiemannStieltjes.lean` is likewise norm-topological and is neither pinned nor a
general PVM. The existing theorem-level ultraweak tagged-sum limits remain useful consequences;
Sakai's printed source topology is the stronger `s(M,M_*)` topology.

## Spectral-integral interface experiment

D002 adds a narrower conclusion. At current-Mathlib commit `2ca39e6`,
`Archive/RiemannStieltjes.lean` is a useful design precedent: its named integral predicate is a
thin wrapper around `BoxIntegral.HasIntegral` only because `BoxIntegral` already owns tagged boxes,
Riemann/Henstock gauges, filter bases, eventual partition results, and a non-bottom theorem. It is
not a usable dependency for Sak-AI because it is absent from pinned Mathlib, norm-topological,
box-based, and its Riemann wrapper is mesh-only.

The endpoint geometry also needs an explicit adapter: Sak-AI's difference of two `Iio` spectral
projections represents `[r,s)`, whereas the box increment infrastructure is organized around its
own box convention. `Finpartition` provides refinement but not tags, ordered real endpoints, mesh,
or atom ownership. `SimpleFunc` does not remove the gap because spectral integration of its fibers
already requires a set-indexed projection assignment.

The scratch proofs further show that an abstract non-bottom canonical filter is not the missing
Mathlib object: after it is built, the proposed generic predicate is exactly `Tendsto`. The missing
content is the integrator's projection/additivity/continuity laws and honest treatment of atoms.
For the next continuous truncated-affine consumer, reuse generic `Tendsto` and the existing
norm-to-ultraweak map rather than adding a local integration hierarchy.

## First-wave general helper

- `IsStarProjection.sub_mul_sub_eq_zero_of_le` is a plausible Mathlib contribution: it is stated
  for nonunital $C^*$-algebras and says that differences from two ordered disjoint intervals in a
  chain of four projections are orthogonal. No equivalent was found in pinned or current Mathlib.

## Intrinsic strong topology and projections

Pinned Mathlib (`476ab284...`), the audited current Mathlib tree, and original LeanOA contain no
equivalent of Sak-AI's predual-indexed `Ultraweak.Strong` topology or the projection convergence
API added for Sakai 1.11.1. The general new results are plausible upstream candidates:

- eventual domination by a limiting projection upgrades ultraweak convergence to strong
  convergence;
- strong seminorm distance is monotone along nested projection intervals;
- the canonical net of a directed projection family converges strongly to its LUB.

They remain in a downstream Sak-AI bridge module because Mathlib currently has no matching
intrinsic topology in which to state them.

## Section 1.12 polar decomposition

Pinned Mathlib has the required canonical `CFC.abs`, sqrt/rpow/inverse/order APIs but no element
polar-decomposition theorem and no `IsPartialIsometry` predicate. Current Mathlib audited at
`be865aa50cc0364be66c3941a6dc0c845a2c2ceb` has the same gap. The audit found no duplicate polar
calculus in Sak-AI or the read-only original LeanOA either. Sak-AI now supplies the general
absolute-value annihilation lemmas `CFC.abs_mul_eq_zero_iff` and `CFC.mul_abs_eq_zero_iff`, plus
the consequences `IsStarProjection.mul_star_mul_self`, `mul_star_mul_self_assoc`, and
`mul_star_self`; these remain plausible upstream candidates. The proof-local regularizer needs no
new Mathlib abstraction: canonical sqrt/rpow/order results prove contractivity and norm
convergence, while Sak-AI's existing specified-predual closed-ball compactness supplies the later
ultraweak cluster point. The reviewed W-star bridge `WStarAlgebra.support_abs` / `support_abs_star`
then reuses Sak-AI's existing support universal properties; no equivalent appears in the audited
trees, and no new Mathlib object is needed. The W-star existence theorem itself belongs in Sak-AI
unless Mathlib first acquires a compatible W-star support/compactness layer. Sak-AI now supplies
that theorem as `WStarAlgebra.exists_element_polar_decomposition`, using a private regularizer and
ultraweak cluster-point proof. The general source consequence
`CFC.mul_star_eq_of_eq_mul_abs` has been placed in the mirrored layer at the abstract nonunital
real-CFC generality of Mathlib's absolute value; it is a small plausible upstream candidate. No
combined element-polar theorem or equivalent cutdown was found in pinned Mathlib, audited current
Mathlib, pre-WS-5 Sak-AI, or original LeanOA. Sak-AI now also supplies
`WStarAlgebra.element_polar_decomposition_unique` and the exact
`WStarAlgebra.existsUnique_element_polar_decomposition`; the former deliberately uses the existing
support zero-kernel and projection-fixing APIs rather than adding a more abstract one-use helper.

## Section 1.13 normality and complete additivity

Pinned and audited current Mathlib provide generic `ScottContinuous`/`ScottContinuousOn`, positive
linear maps, finite sums, and $C^*$-projection algebra, but no $W^*$-predual, ultraweak normality,
arbitrary $W^*$-projection sums, or unique-predual theorem. Sak-AI already has the hard theorem
`PositiveLinearMap.isNormalOnProjections_iff_mem_continuousDual`, directed projection LUB
convergence in both ultraweak and intrinsic strong topologies, and the canonical predual
equivalence. Original LeanOA contains only earlier specified-predual/ultraweak foundations.

The remaining gap is connective rather than foundational: an explicit source-facing equivalence
between Sakai's preservation of bounded directed suprema of all positive elements and the existing
projection-normality predicate, plus finite-partial-sum packaging for arbitrary orthogonal
projection families and the complete-additivity equivalence. Do not use ordinary `tsum` for the
possibly uncountable source sum or introduce a competing normality structure.

## Radon--Stieltjes refinement audit

The exact audit in `reports/RIEMANN_STIELTJES_EXTERNAL_AUDIT.md` confirms that pinned Mathlib already
contains the generic machinery Sak-AI should reuse: `Finset` inclusion/union, `Set.Ici`,
`map_val_Ici_atTop`, `atTop_Ici_eq`, `tendsto_comp_val_Ici_atTop`, metric finite approximations of
totally bounded intervals, and filter-basis nontriviality lemmas. These suffice for prescribed cuts
and for a checked nontrivial refinement-plus-mesh candidate filter.

No audited library supplies the missing semantic object. PNT+'s implemented filter is scalar,
fixed-interval, and mesh-only; teorth's scalar Darboux development has placeholders; current
Mathlib's archived Riemann--Stieltjes API and the ICERM work are fixed-box and norm-topological.
Accordingly the remaining gap is not another generic cofinality theorem. Sakai's source clause is
strong-topological, while its operator-valued division/refinement and improper-limit semantics are
LEVEL C ambiguous. No source-certified representation predicate is currently justified.

## CFC audit for truncated-affine recovery

At pinned Mathlib commit `476ab284`, the public unital CFC is already algebra-and-predicate based:
`ContinuousFunctionalCalculus R A p` supplies the bundled `cfcHom`, while ordinary clients use
`cfc`. Composition, uniqueness, restriction/range, order, and the positive-part identity are all
part of that architecture. Sak-AI's `CStarAlgebra.spectralPositivePart` is therefore intentionally
only a source-facing name for `cfc (fun x : ℝ => (r - x)⁺) a`; its equality with
`(algebraMap ℝ A r - a)⁺` reuses Mathlib's `CFC.posPart_def`, composition, subtraction, constants,
and the identity function.

The new truncated-affine theorem needs no local continuous calculus. Its canonical band estimates
identify finite spectral sums directly with the existing `spectralPositivePart`, and its
ultraweak statement merely transports the already-proved norm limit through `toUltraweak`.
The topology defining CFC and the topology of spectral-sum convergence remain separate.

Current Mathlib commit `e62ea4d7200989bad96e0cc05b349c1a5c9800c8` contains an upstream
`ContinuousFunctionalCalculus/Transfer.lean` substantially matching Sak-AI's pinned staging layer,
as well as interval-norm helpers relevant to the existing local order API. These are future
dependency-update migration candidates, not usable at the pinned revision. During that update,
check the current nonunital transfer namespace spelling before deleting local staging. Neither the
pinned nor audited current tree supplies a general projection-valued measure or an operator-valued
spectral integral.

## External work already monitored

Root `REVIEW_QUEUE.md` records the authoritative status of Mathlib PRs #42093, #42095, and #42100
and the completed overlap audits for Sections 1.10 and 1.11.1. Do not duplicate or silently update
those conclusions here; append only new evidence with commit/revision identifiers.
