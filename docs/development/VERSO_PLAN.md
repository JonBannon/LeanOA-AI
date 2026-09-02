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
should now point to the Section 1.15 topology/API audit and Proposition 1.15.1.

The first Section 1.15 transaction completes the direct source and API audit but does not complete
Proposition 1.15.1. Do not create a theorem node or declaration link for it. The public current
frontier remains Proposition 1.15.1 and should state that the concrete $B(H)$ predual,
$\sigma$-WOT/ultrastrong identifications, and relative Kaplansky closure machinery are still
missing.

If the general topology bridges are mentioned later in the library/API path, distinguish them
precisely: Mathlib's `ContinuousLinearMapWOT` is concrete WOT;
`PointwiseConvergenceCLM` is pointwise/SOT; Sak-AI's `σ(M,P)`, `s(M,P)`, and Mackey topology are
intrinsic specified-predual constructions. `PointwiseConvergenceCLM.toWOT`, its WOT-closed-to-SOT-
closed corollary, and `Strong.isClosed_iff_image_toUltraweakEquiv` introduce no new topology and do
not identify $\sigma$-WOT or ultrastrong topology with the intrinsic types. No Verso mathematical
status should be inferred from these connective API declarations alone.

## Work that must wait

- Do not document a set-indexed spectral measure or spectral integral as formalized until IQ-001 is
  resolved and the linked declaration proves the stated object/theorem.
- Do not expose workstream policy, design contracts, or integration queues in the public manual.
- Do not create a parallel status manifest; use Verso Blueprint metadata and `uses` references.

## Validation

Run the commands in `SAKAI_DESIGN_CONTRACT.md` and inspect the generated graph, summary, search,
index, and manifest whenever mathematical documentation changes.
