# Verso development plan

## Governing architecture

Verso in `docs/` is already the sole mathematical-documentation source. It has exact migration
parity with the retired LeanBlueprint graph and consumes the local theorem package through checked
declaration links. Keep development guidance in repository documents, not the public reading path.

## Work that can proceed behind stable APIs

- Maintain the public `Current frontier` as spectral work advances.
- Add theorem blocks, declaration links, and `uses` edges for integrated spectral-band or tagged-sum
  results when they materially support the mathematical reading path.
- Audit all links and existing prose against current declarations.
- Prepare one systematic conversion of legacy C-star/W-star prose to $C^*$/$W^*$ typography; do
  not perform scattered replacements.
- Preserve the mathematical path, library/API path, graph, summary, search, and index.

The spectral theorem stack now has a public presentation through spectral-band calculus, tagged
spectral sums, truncated-affine weighted convergence to the existing CFC positive part, and the
general fixed-projection ultraweak decomposition used by Sakai's uniqueness argument. Scratch now
kernel-checks a nontrivial refinement-plus-mesh filter and the complete pointwise/family uniqueness
chain under its explicit left-endpoint moment hypothesis. The public frontier must continue to say
that Sakai's source theorem is incomplete: source-equivalence of that candidate with the book's
abstract Radon--Stieltjes integral remains OPEN / RED.

The source-certification audit established that the printed topology is `s(M,M_*)`, not the
ultraweak topology. The exact nonmonotone Lemma 1.11.1 is now kernel-proved and Verso presents it as
such. The overall integral semantics remain LEVEL C because the division, refinement, tag, and
improper-endpoint conventions are not defined and were not uniform in the period literature. Verso
must continue to present the candidate uniqueness theorem only as a clarified scratch analogue,
never as the exact source theorem.

Sakai 1.12.1 is now a public theorem node linked to the exact kernel-proved `ExistsUnique`
declaration. A small Mathlib-tagged absolute-value node records its genuine CFC dependency without
inventing a local absolute-value object. Section 1.12 is complete.

The existing Normality chapter now contains the source-facing bounded directed-positive
characterization, exact Theorem 1.13.2, and arbitrary orthogonal finite-sum/LUB/convergence nodes.
It now also contains the kernel-proved arbitrary-family complete-additivity characterization and
its projection-chain proof dependency, without duplicating Section 1.13 or exposing workstream
policy. Section 1.13 is complete.

The Section 1.14 reading path now includes functional support, Sakai's norm-theoretic Definition
1.14.1, the exact unique orthogonal Jordan decomposition in Theorem 1.14.3, and the source-faithful
general normal-functional polar decomposition in Theorem 1.14.4. Keep the source definition
visibly distinct from the derived support-product-zero characterization. Present 1.14.4 with its
right-action convention, norm, initial support, uniqueness, and final support of
`Ultraweak.functionalAbs` of the adjoint. The older self-adjoint-unitary left factorization is a
dependency, not the general theorem. Section 1.14 is complete, and the public current frontier
now points past the source-formalized Proposition 1.15.1 to Proposition 1.15.2. The next public
addition should follow a direct source/API audit of its bounded-sphere and induced-predual
interfaces. That audit is now complete: “bounded spheres” means norm-closed balls, and the exact
statement is topology-level and net-general. The generic quotient-predual subspace-topology bridge
and the weak-family closed-ball theorem now kernel-check and have a deliberately partial public
node labeled Proposition 1.15.2(1). The positive-square strong-family comparison now also
kernel-checks for arbitrary filters and source-formalizes Proposition 1.15.2(2) on the same
norm-closed balls. Its public node should link the intrinsic-strong/SOT,
ultrastrong/SOT, and intrinsic-strong/ultrastrong homeomorphisms while explicitly denying global
topology equality. The public frontier remains Proposition 1.15.2 until a following transaction
packages the two clauses in Sakai's exact printed order; do not label the full proposition
source-formalized before that declaration exists.

The first Section 1.15 transaction completes the direct source and API audit but does not complete
Proposition 1.15.1. Do not create a theorem node or declaration link for it. The public current
frontier remains Proposition 1.15.1; at that checkpoint the concrete $B(H)$ predual,
$\sigma$-WOT/ultrastrong identifications, and relative Kaplansky closure machinery were still
missing.

The second transaction may be presented as a stable infrastructure node, not as Proposition
1.15.1: the finite vector-functional span is star/multiplier invariant, induces Mathlib WOT in both
directions, and is the full WOT-continuous dual. At that checkpoint the frontier text recorded that
the norm-completed predual, coefficient-series σ-WOT, ultrastrong comparison, and relative
Kaplansky theorem remained missing.

The third transaction is another stable infrastructure node, still not Proposition 1.15.1.  It
computes the coefficient norm, takes the actual norm closure, and proves canonical evaluation is
an isometric equivalence onto its dual by generalized Fréchet--Riesz recovery.  The frontier text
should say that the concrete predual is complete while coefficient-series σ-WOT, ultrastrong, and
relative Kaplansky bridges remain missing.

The fourth transaction is a stable coefficient-series infrastructure node, still not Proposition
1.15.1. It records arbitrary-index norm summability and evaluation, the invariant finite core, the
span of exactly Sakai's countable series, and the continuous identity from the full
concrete-predual topology to the series-test weak topology. The prose must state explicitly that
the converse representation and topology equality are not proved; the frontier now retains the
concrete ultrastrong and ambient-relative Kaplansky bridges.

The fifth transaction is a stable ambient-relative Kaplansky infrastructure node, still not
Proposition 1.15.1. It records the transported test-weak closure, the explicit-target relative
unit-ball theorem, the exact identification of the finite-coefficient test-weak closure with
Mathlib WOT, and the concrete Mackey-density endpoint. The prose must not turn this bounded-set
density result into the five-way global closedness theorem. The frontier now retains only the concrete
ultrastrong/intrinsic-strong bridge among the immediate Proposition 1.15.1 implementation edges;
the converse coefficient-series representation remains deferred to the later source results.

The sixth transaction is a stable concrete-ultrastrong infrastructure node, still not Proposition
1.15.1. It records the square-summable convergence carrier, its continuous identity to
pointwise/SOT, the positive diagonal coefficient-series functional, the exact GNS-seminorm
identity, and the continuous identity from intrinsic strong to concrete ultrastrong convergence.
The prose must explicitly deny the converse and topology equality. The frontier now retains only
the final five-way global closedness assembly; later representation/equality results remain
deferred to their source order.

The seventh transaction is the source proposition node for Sakai 1.15.1. It states all five
global closedness predicates in source order and links the final `List.TFAE` theorem together with
the four named WOT equivalences. Its proof narrative must make the relative Kaplansky unit-ball
argument and scalar normalization visible, and must explicitly deny that the theorem establishes
global equality of the topologies. With this node checked, the public frontier advances to
Proposition 1.15.2; the next documentation transaction begins with a source/API audit rather than
an implementation claim.

If the general topology bridges are mentioned later in the library/API path, distinguish them
precisely: Mathlib's `ContinuousLinearMapWOT` is concrete WOT;
`PointwiseConvergenceCLM` is pointwise/SOT; Sak-AI's `σ(M,P)`, `s(M,P)`, and Mackey topology are
intrinsic specified-predual constructions. `PointwiseConvergenceCLM.toWOT`, its WOT-closed-to-SOT-
closed corollary, and `Strong.isClosed_iff_image_toUltraweakEquiv` do not identify $\sigma$-WOT or
ultrastrong topology with the intrinsic types. The dedicated square-summable carrier is related
globally only by the proved chain intrinsic strong → concrete ultrastrong → pointwise/SOT. On the
norm-closed balls of Proposition 1.15.2(2), the new positive-square argument proves the three
restricted homeomorphisms. Likewise, `WeakBilin.restrictRightL` and its coefficient-series
specialization prove only a global continuous identity, while Proposition 1.15.2(1) supplies the
restricted weak-family homeomorphisms. None of these bounded-carrier results converts the ambient
topologies into global equalities.

## Work that must wait

- Do not document a set-indexed spectral measure or spectral integral as formalized until IQ-001 is
  resolved and the linked declaration proves the stated object/theorem.
- Do not expose workstream policy, design contracts, or integration queues in the public manual.
- Do not create a parallel status manifest; use Verso Blueprint metadata and `uses` references.

## Validation

Run the commands in `SAKAI_DESIGN_CONTRACT.md` and inspect the generated graph, summary, search,
index, and manifest whenever mathematical documentation changes.
