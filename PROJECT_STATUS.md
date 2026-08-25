# LeanOA resumption checkpoint

Recorded 2026-08-24 before pausing work to conserve usage credits.

## Repository state

- Work is on `master`, tracking `origin/master`.
- The starting commit for the next round of work is
  `90ac7afe2f07e41fd63cc69bbc7743ca457aa691` (merge of PR #1).
- No part of the mathematical refactor described below has been started, so there are no
  half-completed Lean edits to recover or disentangle.
- PR #1 incorporated the strict-transparency repair in the normality characterization, the
  documentation dependency repair, and the README links to the project documentation.

The project-wide conventions and design principles remain in `STYLE_GUIDE.md`. In particular,
future work should preserve Mathlib-style proof structure, natural public generality, explicit
maps and compatibility classes rather than definitional-equality dependencies, and reusable lemmas
rather than long local proof scaffolding. Sakai is a fallback proof source rather than a template.

## Approved mathematical refactors

### Nonunital public APIs

Generalize the public normality and specified-predual uniqueness APIs from `CStarAlgebra` to
`NonUnitalCStarAlgebra`. The existence of a specified predual should supply unitality internally.
Keep genuinely unital implementation lemmas private or clearly separated from the public
nonunital interface, and cross any representation boundary through explicit named maps and lemmas.

The main files to inspect are:

- `LeanOA/Ultraweak/IsUnital.lean`
- `LeanOA/Ultraweak/NormalCharacterization.lean`
- `LeanOA/Ultraweak/PredualUniqueness.lean`
- their imported normal-cutoff and polar-decomposition dependencies

Before choosing the implementation, inspect the precise API of
`CStarAlgebra.isUnital_of_predual` and the import graph. Avoid constructing independently
transported instances whose interoperability depends on definitional equality.

### Minimal Zorn hypothesis

Refactor the Zorn argument so its reusable core assumes only the existence of least upper bounds
for nonempty chains. Retain stronger directed-completeness and specified-predual results as
convenient wrappers. Preserve existing public names where that avoids needless downstream churn,
and introduce a new core name only when it improves the API.

The main files to inspect are:

- `LeanOA/Ultraweak/NormalSelection.lean`
- `LeanOA/Ultraweak/ProjectionLattice.lean`

The intended separation is: weakest chain-complete order-theoretic core, then a directed-complete
wrapper, then the operator-algebraic/predual specialization.

## Blueprint and documentation

Update blueprint statements and declaration links after the public Lean APIs settle. The blueprint
should continue to use the nonunital continuous-functional-calculus route; it should not introduce
a full nonunital Gelfand isomorphism with `C₀(X)` unless a real downstream consumer appears.

The documentation workflow now builds successfully, but the published GitHub Pages URLs returned
404 after merging because Pages was not enabled. GitHub rejected enabling Pages while the
repository is private under the current account plan. Publishing therefore requires an explicit
owner decision to make the repository public or use a plan/deployment target supporting private
Pages. This external issue is independent of the generated documentation itself.

## Suggested order on resumption

1. Inspect the declarations and import graph listed above.
2. Implement and target-build the nonunital normality API.
3. Implement and target-build the nonunital uniqueness API.
4. Extract the chain-LUB Zorn core and retain the stronger wrappers.
5. Update `STYLE_GUIDE.md` only if the implementation reveals a genuinely new global principle.
6. Update every affected blueprint statement and `\lean{...}` link.
7. Run the full validation suite:

   ```sh
   lake build
   lake lint
   lake exe mk_all
   leanblueprint all
   leanblueprint checkdecls
   git diff --check
   ```

If a choice about theorem generality, instance ownership, naming, or the public representation
requires human judgment, stop and ask before fixing the API around that choice.
