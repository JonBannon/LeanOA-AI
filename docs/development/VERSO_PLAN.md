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

The first spectral parallel wave now has a three-node public presentation: spectral-band calculus,
tagged spectral sums, and tagged-sum convergence. The last node explicitly separates its stronger
norm and derived ultraweak limits from the still-missing Radon--Stieltjes integral interface.

## Work that must wait

- Do not document a set-indexed spectral measure or spectral integral as formalized until IQ-001 is
  resolved and the linked declaration proves the stated object/theorem.
- Do not expose workstream policy, design contracts, or integration queues in the public manual.
- Do not create a parallel status manifest; use Verso Blueprint metadata and `uses` references.

## Validation

Run the commands in `SAKAI_DESIGN_CONTRACT.md` and inspect the generated graph, summary, search,
index, and manifest whenever mathematical documentation changes.
