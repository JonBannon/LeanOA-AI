# Sakai 1.14.1 and 1.14.3: norm orthogonality and Jordan decomposition

This report records the production formalization of Sakai, Definition 1.14.1 and Theorem 1.14.3.
The direct source reconstruction and overlap audit are in
`SAKAI_1_14_1_1_14_3_SOURCE.md`.

## Definition 1.14.1

For positive linear functionals `phi` and `psi` on a $C^*$-algebra, Sakai defines orthogonality by

```text
‖phi - psi‖ = ‖phi‖ + ‖psi‖.
```

The production definition is `PositiveLinearMap.IsOrthogonal`. It is stated at the natural
nonunital $C^*$-algebra level and has no normality, support, predual, or $W^*$-algebra assumption.
`PositiveLinearMap.isOrthogonal_comm` records symmetry. Orthogonality of support projections is
not the definition.

## Theorem 1.14.3

Sakai assumes a $W^*$-algebra `M` and a self-adjoint functional `f` in its predual. He proves that
there are unique normal positive functionals `f1` and `f2` satisfying

```text
f = f1 - f2
‖f‖ = ‖f1‖ + ‖f2‖.
```

`Ultraweak.existsUnique_orthogonal_decomposition_of_isSelfAdjoint` is the exact source-facing
package. Its input is `f : σ(M, P) →L[ℂ] ℂ` with
`IsSelfAdjoint (WithConv.toConv f)`. Its unique pair consists of ordinary positive maps
`M →ₚ[ℂ] ℂ`, carries explicit `IsNormalOnProjections` proofs, decomposes
`f.comp (toUltraweakL ℂ M P)`, and satisfies `PositiveLinearMap.IsOrthogonal`. The induced map on
`M` is used because that is where the source operator norm is available.

## Existing factorization

The proof reuses `Ultraweak.exists_positive_comp_mulLeft_of_isSelfAdjoint`. That theorem supplies a
self-adjoint unitary `u`, a positive ultraweakly continuous functional `phi`, and the factorization
`f = phi.toContinuousLinearMap.comp (Ultraweak.mulLeftL (P := P) u)`. It already encapsulates the
compact exposed-face argument in Sakai's existence proof.

No competing polar decomposition was introduced. This self-adjoint-unitary factorization is an
input to Theorem 1.14.3; it is not Sakai's Theorem 1.14.4, which concerns an arbitrary normal
functional and a partial isometry.

## Functional support use

Existence does not require functional support. Uniqueness reuses the Section 1.14.2 API, especially
`PositiveLinearMap.support_le_iff_apply_eq_apply_one` and the support cutdown identities. The
direct structural implication is
`PositiveLinearMap.isOrthogonal_of_support_mul_eq_zero`; after uniqueness is available,
`PositiveLinearMap.support_mul_eq_zero_of_isOrthogonal` proves the converse and
`PositiveLinearMap.isOrthogonal_iff_support_mul_eq_zero` packages the equivalence.

Thus support-product zero characterizes source orthogonality for normal positive functionals on a
$W^*$-algebra. It does not replace Sakai's norm-theoretic definition.

## Construction

From the self-adjoint unitary `u`, the private construction forms the complementary star
projections

```text
p = (1 + u) / 2,    q = 1 - p.
```

Self-adjointness of `f` implies that the positive factor centralizes `u` at the functional level.
The two positive pieces are then obtained by composing with
`IsStarProjection.Corner.ultraweakCutdownP` for `p` and `q`, followed by the existing pullback from
the ultraweak topology to `M`. Projection splitting, centrality, and carrier witnesses remain
private implementation details.

## Normality

Each cutdown is a positive ultraweakly continuous map. Pulling it back along
`Ultraweak.toUltraweakPosCLM` produces an ordinary positive functional, and
`PositiveLinearMap.isNormalOnProjections_of_mem_continuousDual` supplies its explicit normality
proof. No normal-functional wrapper or second normality predicate was added.

## Orthogonality

The exact norm identity gives Sakai orthogonality directly after rewriting by the difference
decomposition. Separately, the complementary carrier equalities imply that the two functional
supports lie below complementary projections, hence their product is zero; this private
support-bearing decomposition is used for the converse support theorem.

Conversely, `PositiveLinearMap.support_mul_eq_zero_of_isOrthogonal` uses the already-proved unique
Jordan decomposition, rather than assuming the desired characterization inside uniqueness.
`PositiveLinearMap.isOrthogonal_iff_support_mul_eq_zero` is therefore noncircular.

## Norm identity

The construction proves the exact source formula

```text
‖f.comp (toUltraweakL ℂ M P)‖ =
  ‖f1.toContinuousLinearMap‖ + ‖f2.toContinuousLinearMap‖.
```

The proof uses the norm isometry from multiplication by the unitary and
`PositiveContinuousLinearMap.ofReal_opNorm_eq_map_one` for the positive factor and its two
cutdowns. Rewriting by the difference decomposition turns this equality into
`f1.IsOrthogonal f2` without changing Sakai's definition.

## Uniqueness

The private existence theorem retains the source carrier equalities at `p` and `1 - p`. For any
competing normal positive pair with the same difference and norm-additive decomposition,
evaluation at `1` first identifies the component norms. Evaluation at the complementary carriers,
`PositiveLinearMap.support_le_iff_apply_eq_apply_one`, and the Section 1.14.2 cutdown identities
then identify both functionals. The public theorem exposes only the resulting exact `∃!` pair.

This proof does not use the converse “norm orthogonality implies support-product zero”; that
converse is derived afterward from uniqueness.

## Public API decision

The public surface added by this wave is deliberately theorem-sized:

- `PositiveLinearMap.IsOrthogonal`;
- `PositiveLinearMap.isOrthogonal_comm`;
- `PositiveLinearMap.support_le_iff_apply_eq_apply_one`;
- `PositiveLinearMap.isOrthogonal_of_support_mul_eq_zero`;
- `Ultraweak.existsUnique_orthogonal_decomposition_of_isSelfAdjoint`;
- `PositiveLinearMap.support_mul_eq_zero_of_isOrthogonal`;
- `PositiveLinearMap.isOrthogonal_iff_support_mul_eq_zero`.

There are no public choice-based `positivePart` or `negativePart` definitions, no Jordan
decomposition structure, no new normal-functional type, and no second functional polar
decomposition. A downstream consumer may justify canonical part definitions later.

## Downstream dependencies

Definition 1.14.1 and Theorem 1.14.3 are complete. The next bounded source frontier is Sakai,
Theorem 1.14.4: polar decomposition of an arbitrary normal functional, including the source norm
identity and the partial-isometry support conditions. Its implementation should first audit and
reuse the existing functional factorization and the completed functional-support/Jordan APIs; the
self-adjoint-unitary theorem used here must not be relabeled as Theorem 1.14.4.
