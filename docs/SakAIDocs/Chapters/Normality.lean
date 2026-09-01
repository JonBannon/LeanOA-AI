import Verso
import VersoManual
import VersoBlueprint
import LeanOA

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Normality and ultraweak continuity" =>

Let $`M` be a possibly nonunital C-star algebra with a specified Banach
predual $`P`.  The predual forces $`M` to be unital, but the public statements
do not assume a unit separately.  This chapter proves that a positive
functional is normal on projections exactly when it is represented by $`P`,
and uses that intrinsic characterization to prove uniqueness of the predual.

{index}[normal functional]
{index}[ultraweakly continuous functional]
{index}[predual, uniqueness]

:::definition "def:normal_on_projections" (lean := "PositiveLinearMap.IsNormalOnProjections")
For a positive linear map $`f`, _normality on projections_ is Scott
continuity of the induced map on the subtype of star projections.  Thus $`f`
preserves least upper bounds of nonempty directed families of projections.
The formal definition is order-theoretic and assumes neither a topology nor a
C-star algebra.
:::

:::definition "def:normal_positive_Sak_1_13_1" (lean := "PositiveLinearMap.isNormalOnProjections_iff_scottContinuousOn_bounded_nonneg, ScottContinuousOn.bounded_nonneg_iff_nonneg") (uses := "def:normal_on_projections")
Sakai calls a positive functional $`\varphi` _normal_ when it preserves the
least upper bound of every uniformly norm-bounded, nonempty directed family of
positive elements.  In Lean this is `ScottContinuousOn` restricted to bounded
nonnegative sets.  It is equivalent to the established projection-normality
predicate.  The printed boundedness clause is retained explicitly, although it
is automatic once a nonnegative set has a least upper bound.
:::

:::definition "def:specified_ultraweak_dual" (lean := "Ultraweak.continuousDual, Ultraweak.mem_continuousDual_iff_exists_comp_toUltraweakL") (uses := "def:sigma_top")
The _continuous dual represented by $`P`_ is the norm-closed subspace of
$`M^*` given by the image of the canonical isometric embedding of $`P`.  A
norm-continuous functional belongs to it precisely when it factors through
the explicit map from $`M` to its $`\sigma(M,P)` topology.
This is also the established Lean object representing Sakai Definition
1.13.5: its elements are the arbitrary (not necessarily positive) normal
linear functionals.
:::

:::group "normal-easy-direction"
Ultraweak continuity implies normality.
:::

# Ultraweak continuity implies normality
%%%
tag := "normal-easy-direction"
%%%

:::lemma_ "lem:homeo_of_cts_bij_cpt_haus" (parent := "normal-easy-direction") (lean := "isHomeomorph_iff_continuous_bijective") (tags := "mathlib")
A continuous bijection from a compact space to a Hausdorff space is a
homeomorphism.
:::

:::proof "lem:homeo_of_cts_bij_cpt_haus"
This is the standard compact-to-Hausdorff closed-map argument supplied by
Mathlib.
:::

:::theorem "thm:Banach_Alaoglu" (parent := "normal-easy-direction") (lean := "WeakDual.isCompact_closedBall") (tags := "mathlib")
The closed unit ball of the continuous dual of a normed space is compact for
the weak-star topology.
:::

:::proof "thm:Banach_Alaoglu"
This is Mathlib's Banach--Alaoglu theorem.
:::

:::theorem "lem:sigma_cont_of_normal_Sak_1_7_4" (parent := "normal-easy-direction") (lean := "Ultraweak.DirectedOn.exists_isLUB_of_isBounded, Ultraweak.DirectedOn.isLUB_star_right_conjugate") (uses := "thm:Banach_Alaoglu, lem:homeo_of_cts_bij_cpt_haus, lem:uw_pos_sep_pts, lem:selfadjoint_le_norm, def:sigma_top")
Every norm-bounded increasing net of self-adjoint elements converges
ultraweakly to its least upper bound.  If $`x=\sup_\lambda x_\lambda`, then
$`a^*xa=\sup_\lambda a^*x_\lambda a` for every $`a\in M`.
:::

:::proof "lem:sigma_cont_of_normal_Sak_1_7_4"
Let $`T` be the ultraweakly continuous positive functionals and $`E` their
linear span.  Positive separation makes $`E` point separating, so
$`\sigma(M,E)` is Hausdorff.  On a norm ball the identity from
$`\sigma(M,P)` to $`\sigma(M,E)` is a continuous bijection from a compact
space to a Hausdorff space, hence a homeomorphism.  Evaluating an increasing
bounded net against every member of $`T` gives bounded increasing real nets,
so the original net is ultraweak Cauchy.  Compactness supplies its limit, and
positive separation identifies that limit with the least upper bound.

Conjugation by an invertible element preserves least upper bounds.  For a
general $`a`, shift by a sufficiently large scalar to make $`c1+a`
invertible and expand its conjugation.  Cauchy--Schwarz controls the cross
terms, using the norm bound on the increasing net; after taking limits, the
quadratic term gives preservation under $`x\mapsto a^*xa`.
:::

:::theorem "thm:uw_continuous_is_normal" (parent := "normal-easy-direction") (lean := "PositiveLinearMap.isNormalOnProjections_of_mem_continuousDual") (uses := "def:normal_on_projections, def:specified_ultraweak_dual, lem:sigma_cont_of_normal_Sak_1_7_4, prop:proj_compl_lat_wstar_Sak_1_10_2")
If a positive functional is represented by $`P`, equivalently is
$`\sigma(M,P)`-continuous, then it is normal on projections.
:::

:::proof "thm:uw_continuous_is_normal"
A nonempty directed family of projections converges ultraweakly to any
specified least upper bound.  Factoring the functional through the
ultraweak topology gives convergence of its values; positivity makes those
values monotone, so their limit is their least upper bound.
:::

:::group "normal-hard-direction"
Normality implies representation by the specified predual.
:::

# Normality implies ultraweak continuity
%%%
tag := "normal-hard-direction"
%%%

:::lemma_ "lem:exists_uw_ge_normal" (parent := "normal-hard-direction") (lean := "Ultraweak.exists_positiveCLM_apply_gt") (uses := "lem:uw_pos_sep_pts")
For every positive functional $`\varphi` and every nonzero positive element
$`a`, there is a positive ultraweakly continuous functional $`\psi` with
$`\varphi(a)<\psi(a)`.  Normality of $`\varphi` is not needed.
:::

:::proof "lem:exists_uw_ge_normal"
Positive separation gives an ultraweakly continuous positive $`\psi_0` with
$`\psi_0(a)\neq0`; positivity makes the value strictly positive.  A
sufficiently large positive integral multiple of $`\psi_0` dominates
$`\varphi` at $`a`.
:::

:::lemma_ "lem:msr_th_lemma" (parent := "normal-hard-direction") (lean := "PositiveLinearMap.IsNormalOnProjections.exists_nonzero_subprojection_lt_of_chain_lubs, PositiveLinearMap.IsNormalOnProjections.exists_nonzero_subprojection_lt, PositiveLinearMap.IsNormalOnProjections.exists_nonzero_subprojection_lt_of_predual") (uses := "def:normal_on_projections, prop:proj_compl_lat_wstar_Sak_1_10_2, cor:proj_sub_of_subproj")
Let $`\varphi` and $`\psi` be positive functionals normal on projections.  If
$`p` is a projection with $`\varphi(p)<\psi(p)`, there is a nonzero
projection $`p_1\leq p` such that
$`\varphi(q)<\psi(q)` for every nonzero projection $`q\leq p_1`.
:::

:::proof "lem:msr_th_lemma"
Let $`S` be the subprojections $`q\leq p` satisfying
$`\psi(q)\leq\varphi(q)`.  Normality preserves this condition under suprema
of chains, so Zorn gives a maximal $`q_0\in S`; strictness at $`p` implies
$`q_0\neq p`.  Set $`p_1=p-q_0`.  A nonzero $`q\leq p_1` violating the
desired inequality would be orthogonal to $`q_0`, and $`q_0+q` would be a
strictly larger member of $`S`, a contradiction.  The formal core only asks
for chain suprema; wrappers expose the directed-complete and predual forms.
:::

:::lemma_ "lem:zorn_base" (parent := "normal-hard-direction") (lean := "PositiveLinearMap.IsNormalOnProjections.isUltraweakCutoff_of_isLUB, PositiveLinearMap.IsNormalOnProjections.exists_maximal_isUltraweakCutoff") (uses := "def:normal_on_projections, def:specified_ultraweak_dual, cor:proj_sub_of_subproj, prop:proj_compl_lat_wstar_Sak_1_10_2")
Let $`\varphi` be positive and normal on projections, and let $`Q(p)` mean
that $`x\mapsto\varphi(xp)` is represented by $`P`.  The predicate $`Q` is
closed under least upper bounds of nonempty directed families of projections.
Consequently there is a maximal projection $`p_0` satisfying $`Q(p_0)`.
:::

:::proof "lem:zorn_base"
For comparable projections $`q\leq p`, Cauchy--Schwarz gives
$`\lVert\varphi(\mathord\cdot(p-q))\rVert\leq
\sqrt{\lVert\varphi\rVert}\sqrt{|\varphi(p-q)|}`.  Normality makes the
right side tend to zero along a directed family with supremum $`p`, so the
cutoffs at its members converge in operator norm to the cutoff at $`p`.
The subspace `Ultraweak.continuousDual` is norm closed, proving closure of
$`Q`.  Completeness of the projection lattice and Zorn's lemma then provide a
maximal projection.
:::

:::theorem "thm:sigma_cts_of_normal_Sak_1_13_2" (parent := "normal-hard-direction") (lean := "PositiveLinearMap.scottContinuousOn_bounded_nonneg_iff_mem_continuousDual, PositiveLinearMap.isNormalOnProjections_iff_scottContinuousOn_bounded_nonneg") (uses := "def:normal_positive_Sak_1_13_1, def:normal_on_projections, def:specified_ultraweak_dual, thm:uw_continuous_is_normal, lem:zorn_base, lem:exists_uw_ge_normal, lem:msr_th_lemma, lem:cut_down_sigma_closed_cts, thm:real_rank_zero_of_predual, cor:positive_functional_le_of_projection_le, lem:bdd_sigma_cts_iff_bdd_s_cts_Sak_1_8_10")
For a positive functional $`\varphi` on $`M`, the following are equivalent:

1. $`\varphi` preserves least upper bounds of uniformly bounded increasing
   directed families of positive elements, in the sense of Sakai 1.13.1;
2. $`\varphi` is represented by $`P`, equivalently it is
   $`\sigma(M,P)`-continuous.

The order-theoretic condition is also equivalent to full Scott continuity of
$`\varphi` and to normality on projections.  Thus the source definition, the
canonical Sak-AI predicate, and the specified-predual characterization agree
without replacing directed families by sequences.
:::

:::proof "thm:sigma_cts_of_normal_Sak_1_13_2"
The reverse implication is the preceding easy direction.  Suppose
$`\varphi` is normal and choose a maximal projection $`p_0` whose cutoff is
represented by $`P`.  If $`p_0\neq1`, positive separation gives an
ultraweakly continuous positive $`\psi` with
$`\varphi(1-p_0)<\psi(1-p_0)`.  It is normal by the easy direction.  The
selection lemma produces a nonzero $`p\leq1-p_0` such that
$`\varphi(q)<\psi(q)` for every nonzero $`q\leq p`.

The analytic corner $`pMp` has a specified predual and hence real rank zero.
The inequality on its projections extends to its whole positive cone.  Apply
it to $`px^*xp` and combine Cauchy--Schwarz with continuity of cutdown: the
cutoff at $`p_0+p` is strong-continuous, hence ultraweakly continuous by the
bounded continuity theorem.  But $`p_0+p` is a projection strictly above
$`p_0`, contradicting maximality.  Therefore $`p_0=1`, whose cutoff is
$`\varphi` itself.
:::

:::group "predual-uniqueness"
The intrinsic continuous dual and uniqueness of Banach preduals.
:::

# Uniqueness of the predual
%%%
tag := "predual-uniqueness"
%%%

:::theorem "thm:unique_predual" (parent := "predual-uniqueness") (lean := "Ultraweak.continuousDual_eq, Predual.equiv, Predual.equiv_apply_duality, Predual.equiv_eq_of_apply_duality_eq") (uses := "def:specified_ultraweak_dual, thm:sigma_cts_of_normal_Sak_1_13_2, thm:polar_decomposition_ultraweak_functional, lem:star_left_mul_right_mul_sig_cts_Sak_1_7_8")
If $`P` and $`Q` are two specified Banach preduals of the same C-star algebra
$`M`, their represented closed subspaces of $`M^*` are equal.  Consequently
there is a canonical complex-linear isometric equivalence
$`E_{P,Q}:P\cong Q` satisfying
$`\langle x,E_{P,Q}(p)\rangle_Q=\langle x,p\rangle_P`.  This evaluation
identity uniquely characterizes the equivalence.
:::

:::proof "thm:unique_predual"
Take a functional represented by $`P` and split it into self-adjoint real and
imaginary parts.  Polar decomposition writes each part as
$`\varphi\circ L_u`, with $`\varphi` positive and $`P`-ultraweakly
continuous and $`u` a self-adjoint unitary.  Normality of $`\varphi` is
intrinsic to the projection order, so the normality characterization makes it
$`Q`-ultraweakly continuous as well.  Left multiplication by $`u` is
$`Q`-ultraweakly continuous; hence the original functional is represented by
$`Q`.  Symmetry proves equality of the two subspaces of $`M^*`.

Both preduals embed linearly and isometrically onto this common subspace.
Compose one identification with the inverse of the other.  The construction
preserves evaluation, and injectivity of the embedding into $`M^*` makes that
property unique.
:::

:::group "orthogonal-projection-sums"
Arbitrary orthogonal families and their finite-subset nets.
:::

# Orthogonal projection sums
%%%
tag := "orthogonal-projection-sums"
%%%

:::definition "def:orthogonal_projection_sum_Sak_1_13_4" (parent := "orthogonal-projection-sums") (lean := "IsStarProjection.orthogonalFinsetSum, IsStarProjection.isLUB_range_orthogonalFinsetSum, IsStarProjection.isLUB_range_coe_orthogonalFinsetSum") (uses := "prop:proj_compl_lat_wstar_Sak_1_10_2")
Let $`(p_i)_{i\in I}` be an arbitrary pairwise orthogonal family of
projections.  For a finite subset $`J\subseteq I`, put
$`P_J=\sum_{i\in J}p_i`.  Each $`P_J` is a projection, inclusion of finite
subsets makes $`J\mapsto P_J` increasing, and its least upper bound is
$`\sup_{J\subseteq_{\mathrm{fin}} I} P_J=\bigvee_{i\in I}p_i`.

This least upper bound in the canonical projection lattice is also the least
upper bound in the ambient $`C^*`-algebra.  It is Sakai's definition of the
sum of the arbitrary orthogonal family; no countability or `tsum` semantics is
used.
:::

:::proof "def:orthogonal_projection_sum_Sak_1_13_4"
Mathlib's finite orthogonal-idempotent theorem gives idempotence of every
partial sum, while self-adjointness is preserved by finite sums.  Product
identities show monotonicity under inclusion.  Every partial sum lies below
$`\bigvee_i p_i`; conversely, any projection above all partial sums is above
each singleton sum $`p_i`, hence above their supremum.
:::

:::theorem "thm:orthogonal_projection_sum_convergence_Sak_1_13_4" (parent := "orthogonal-projection-sums") (lean := "IsStarProjection.tendsto_toUltraweak_orthogonalFinsetSum, IsStarProjection.tendsto_toStrong_orthogonalFinsetSum") (uses := "def:orthogonal_projection_sum_Sak_1_13_4, prop:proj_compl_lat_wstar_Sak_1_10_2, def:sigma_top, def:strong_top")
The finite partial sums $`P_J`, indexed by all finite subsets of the arbitrary
type $`I` and ordered by inclusion, converge to $`\bigvee_i p_i` both
ultraweakly and in the intrinsic strong topology $`s(M,P)`.
:::

:::proof "thm:orthogonal_projection_sum_convergence_Sak_1_13_4"
The range of the monotone finite-sum net is a nonempty directed family of
projections with the preceding least upper bound.  The established projection
LUB theorems give ultraweak and strong convergence of its canonical range net.
The map from finite subsets to that range is cofinal, so precomposition gives
the stated convergence of $`J\mapsto P_J` itself.
:::

Sakai continues by characterizing normality through complete additivity on
these arbitrary orthogonal families.  The forward implication and the exact
unconditional scalar-sum semantics are kernel-checked in scratch.  The
converse still requires a maximal orthogonal decomposition of projection
chains, so no production complete-additivity predicate is claimed here.
