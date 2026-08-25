# LeanOA refactor checkpoint

Recorded 2026-08-25 after completing the mathematical refactors planned in the previous
checkpoint.

## Repository state

- Work is on `master`, based on `cbf612c` (`ci: disable the docgen docs cache to stop it dropping
  our API docs`).
- The implementation continues to follow `STYLE_GUIDE.md`: public statements use their natural
  generality, representation boundaries are crossed through named maps, and no proof relies on
  independently transported structures being definitionally equal.

## Completed mathematical refactors

### Nonunital public APIs

The public normality and specified-predual uniqueness APIs now assume
`NonUnitalCStarAlgebra`. A specified predual supplies `IsUnital` inside the proofs, and
`IsUnital.toCStarAlgebra` upgrades the existing algebra structure in place for the genuinely
unital implementation steps.

The affected public surface includes:

- `PositiveLinearMap.isNormalOnProjections_of_mem_continuousDual`;
- `PositiveLinearMap.IsNormalOnProjections.exists_maximal_isUltraweakCutoff`;
- `PositiveLinearMap.IsNormalOnProjections.exists_nonzero_subprojection_lt_of_predual`;
- `PositiveLinearMap.isNormalOnProjections_iff_mem_continuousDual`;
- `Ultraweak.continuousDual_eq` and `Ultraweak.continuousDualCongr`;
- `Predual.equiv` and its pairing-preservation and uniqueness theorems.

The unital cutoff estimate used by the hard implication and the polar-decomposition comparison
remain isolated as unital implementation results.

### Minimal Zorn hypothesis

`PositiveLinearMap.IsNormalOnProjections.exists_nonzero_subprojection_lt_of_chain_lubs` is the
new reusable core. It assumes only least upper bounds for nonempty chains of projections, exactly
the completeness needed by Zorn's lemma.

The previous name `exists_nonzero_subprojection_lt` remains as a directed-complete compatibility
wrapper. `exists_nonzero_subprojection_lt_of_predual` remains the operator-algebraic convenience
wrapper and obtains a complete projection lattice from the specified predual.

## Blueprint and validation

`blueprint/src/BlueprintFiles/NormalityandSigmaWeak.tex` now states the possibly nonunital public
boundary, explains the internal unitality step, and links the chain-complete core and both wrappers.

The following checks passed after the refactor:

```sh
lake build
lake lint
lake exe mk_all
leanblueprint all
leanblueprint checkdecls
git diff --check
```

No update to `STYLE_GUIDE.md` was needed; the implementation follows principles already recorded
there.
