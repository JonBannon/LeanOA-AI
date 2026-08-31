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

The source-certification audit further establishes that the printed topology is `s(M,M_*)`, not
the ultraweak topology. It classifies the overall integral semantics LEVEL C because the division,
refinement, tag, and improper-endpoint conventions are not defined and were not uniform in the
period literature. Verso should present the existing ultraweak result as a proved consequence and
the candidate uniqueness theorem as a clarified scratch analogue, never as the exact source
theorem.

## Work that must wait

- Do not document a set-indexed spectral measure or spectral integral as formalized until IQ-001 is
  resolved and the linked declaration proves the stated object/theorem.
- Do not expose workstream policy, design contracts, or integration queues in the public manual.
- Do not create a parallel status manifest; use Verso Blueprint metadata and `uses` references.

## Validation

Run the commands in `SAKAI_DESIGN_CONTRACT.md` and inspect the generated graph, summary, search,
index, and manifest whenever mathematical documentation changes.
