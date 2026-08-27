import Verso
import VersoManual
import VersoBlueprint
import LeanOA

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Kaplansky density" =>

Write $`S_M=\{x\in M\mid\lVert x\rVert\leq1\}` for the closed unit ball.
Sakai calls this the unit sphere, but Mathlib distinguishes spheres from
closed balls.  The main theorem is first stated for a dense invariant test
space inside a specified predual; the familiar ultraweak version follows by
taking the whole predual.

{index}[Kaplansky density]
{index}[closed unit ball]
{index}[Sakai-invariant test space]

:::group "density-functional-analysis"
General dual-pairing and convex-closure infrastructure.
:::

# Convexity and dual-pairing infrastructure
%%%
tag := "density-functional-analysis"
%%%

:::theorem "thm:krein_milman" (parent := "density-functional-analysis") (lean := "closure_convexHull_extremePoints") (tags := "mathlib")
If $`K` is a compact convex subset of a Hausdorff locally convex real
topological vector space, then $`K` is the closure of the convex hull of its
extreme points.
:::

:::proof "thm:krein_milman"
This is Mathlib's Krein--Milman theorem.
:::

:::theorem "thm:convex_closure_same_dual" (parent := "density-functional-analysis") (lean := "LinearEquiv.image_closure_of_convex'") (tags := "mathlib")
Suppose linearly equivalent complex vector spaces carry locally convex
topologies whose continuous duals are identified by precomposition with the
equivalence.  The equivalence commutes with closure of every real-convex set.
In particular, compatible weak and Mackey topologies have the same closed
convex sets.
:::

:::proof "thm:convex_closure_same_dual"
Mathlib transports both closures to the weak topology and applies geometric
Hahn--Banach separation.
:::

:::lemma_ "lem:bounded_weak_topologies_agree" (parent := "density-functional-analysis") (lean := "WeakBilin.tendsto_of_denseRange_of_eventually_norm_le")
Let $`B:M\times P\to\mathbb C` be a bounded dual pairing and let $`V` be a
norm-dense complex-linear subspace of $`P`.  On every norm-bounded subset of
$`M`, convergence against $`V` is equivalent to convergence against all of
$`P`.  Thus $`\sigma(M,V)` and $`\sigma(M,P)` induce the same topology on
each closed norm ball.
:::

:::proof "lem:bounded_weak_topologies_agree"
Only one implication needs proof.  Approximate a given $`p\in P` in norm by
$`v\in V`.  Boundedness of the net controls the evaluation error
$`|B(x,p-v)|` uniformly, while convergence against $`v` controls the
remaining term.  The formal result lives at the general bounded-dual-pairing
level.
:::

:::lemma_ "lem:mackey_continuous_of_dual_map" (parent := "density-functional-analysis") (lean := "Mackey.map")
Let $`B:E\times F\to\mathbb C` and $`B':E'\times F'\to\mathbb C` be
separating dual pairings.  If linear maps $`T:E\to E'` and $`T':F'\to F`
satisfy $`B'(Tx,y)=B(x,T'y)`, then $`T` is continuous from
$`\tau(E,F)` to $`\tau(E',F')`.
:::

:::proof "lem:mackey_continuous_of_dual_map"
Map an absolutely convex weakly compact subset of $`F'` along $`T'`.  Its
image retains those properties, and the adjointness identity identifies the
corresponding Mackey seminorms.  This is the functorial map theorem in the
general `Mackey` API, not an operator-algebra specialization.
:::

:::group "invariant-test-spaces"
Dense predual subspaces stable under the operator-algebra actions.
:::

# Sakai-invariant test spaces
%%%
tag := "invariant-test-spaces"
%%%

:::definition "def:sakai_invariant_test_space" (parent := "invariant-test-spaces") (lean := "Ultraweak.SakaiInvariantTestSpace")
For a C-star algebra $`M` with specified predual $`P`, a
_Sakai-invariant test space_ is a norm-dense complex subspace $`V\subseteq P`
closed under the dual actions induced by star and fixed left and right
multiplication.  Thus the functionals
$`x\mapsto\overline{v(x^*)}`, $`x\mapsto v(ax)`, and $`x\mapsto v(xa)` are
again represented by $`V`.

This is a predicate on a submodule, not a typeclass: one predual may contain
many useful test spaces and instance search should not choose one globally.
:::

:::lemma_ "lem:tau_continuity_of_sakai_invariant" (parent := "invariant-test-spaces") (lean := "Ultraweak.SakaiInvariantTestSpace.mackeyMulLeftL, Ultraweak.SakaiInvariantTestSpace.mackeyMulRightL, Ultraweak.SakaiInvariantTestSpace.mackeyStarL") (uses := "def:sakai_invariant_test_space, lem:mackey_continuous_of_dual_map")
If $`V` is Sakai-invariant, then star and the maps $`x\mapsto ax` and
$`x\mapsto xa` are continuous for $`\tau(M,V)`.
:::

:::proof "lem:tau_continuity_of_sakai_invariant"
Apply functoriality of the Mackey topology to each operation and its induced
map on $`V`.  Because star is conjugate-linear, its formal continuity uses
the existing topological-star interface rather than forcing it into a
complex-linear map.
:::

:::group "kaplansky-transform"
The C-star-algebraic contraction transform.
:::

# The contraction transform
%%%
tag := "kaplansky-transform"
%%%

For $`a\in M`, Sakai's contraction transform is
$`\kappa(a)=2a(1+a^*a)^{-1}`.  Its algebraic properties do not depend on a
predual.

:::definition "def:kaplansky_transform" (parent := "kaplansky-transform") (lean := "CStarAlgebra.kaplanskyTransform")
For $`a` in a unital C-star algebra, define the _Kaplansky contraction
transform_ by $`\kappa(a)=2a(1+a^*a)^{-1}`.
:::

:::proposition "prop:kaplansky_transform_mem_closedBall" (parent := "kaplansky-transform") (lean := "CStarAlgebra.isUnit_one_add_star_mul_self, CStarAlgebra.kaplanskyTransform_mem_closedBall") (uses := "def:kaplansky_transform")
For every $`a`, the element $`1+a^*a` is invertible and
$`\lVert\kappa(a)\rVert\leq1`.
:::

:::proof "prop:kaplansky_transform_mem_closedBall"
Positivity gives $`1\leq1+a^*a` and hence invertibility.  Continuous
functional calculus reduces the norm estimate to
$`2\sqrt t/(1+t)\leq1` for $`t\geq0`.
:::

:::lemma_ "lem:kaplansky_transform_mem_subalgebra" (parent := "kaplansky-transform") (lean := "CStarAlgebra.kaplanskyTransform_mem_nonUnitalStarSubalgebra") (uses := "def:kaplansky_transform, prop:kaplansky_transform_mem_closedBall")
Let $`A` be a norm-closed, possibly nonunital star subalgebra of a unital
C-star algebra $`M`.  If $`a\in A`, then $`\kappa(a)\in A\cap S_M`.
:::

:::proof "lem:kaplansky_transform_mem_subalgebra"
Express the transform through nonunital continuous functional calculus using
a scalar function that vanishes at the distinguished point.  This avoids
adjoining an identity and matches Mathlib's nonunital subalgebra API.
:::

:::lemma_ "lem:kaplansky_transform_fixed_on_extreme" (parent := "kaplansky-transform") (lean := "CStarAlgebra.kaplanskyTransform_eq_self_of_mem_extremePoints_unitClosedBall") (uses := "def:kaplansky_transform, lem:extreme_partial_isom")
If $`u` is an extreme point of $`S_M`, then $`\kappa(u)=u`.
:::

:::proof "lem:kaplansky_transform_fixed_on_extreme"
The extreme-point lemma makes $`p=u^*u` a projection.  Since
$`(1+p)^{-1}=1-\tfrac12p` and $`up=u`, direct calculation gives
$`2u(1+p)^{-1}=u`.
:::

:::group "kaplansky-density"
Density of the unit ball in the Mackey, strong, and ultraweak topologies.
:::

# The density theorem
%%%
tag := "kaplansky-density"
%%%

:::proposition "prop:kaplansky_transform_in_ball_closure" (parent := "kaplansky-density") (lean := "Ultraweak.SakaiInvariantTestSpace.kaplanskyTransform_mem_ultraweak_closure") (uses := "def:sakai_invariant_test_space, lem:bounded_weak_topologies_agree, thm:convex_closure_same_dual, lem:tau_continuity_of_sakai_invariant, prop:kaplansky_transform_mem_closedBall, lem:kaplansky_transform_mem_subalgebra")
Let $`V\subseteq P` be Sakai-invariant, and let $`A` be a norm-closed star
subalgebra of $`M` dense for $`\sigma(M,V)`.  Then for every $`a\in M`,
$`\kappa(a)` belongs to the $`\sigma(M,P)`-closure of $`A\cap S_M`.
:::

:::proof "prop:kaplansky_transform_in_ball_closure"
The linear subspace $`A` is convex, so compatible weak and Mackey topologies
have the same closure on it.  Choose a net $`a_i\in A` converging to $`a` for
$`\tau(M,V)`.  Sakai's resolvent calculation and continuity of the invariant
operations give $`\kappa(a_i)\to\kappa(a)` in $`\sigma(M,V)`.  Each transform
lies in $`A\cap S_M`, and bounded weak-topology agreement upgrades the
convergence to $`\sigma(M,P)`.
:::

:::theorem "thm:kaplansky_density_Sak_1_9_1" (parent := "kaplansky-density") (lean := "Ultraweak.SakaiInvariantTestSpace.kaplansky_density_Sak_1_9_1") (uses := "thm:krein_milman, thm:convex_closure_same_dual, prop:kaplansky_transform_in_ball_closure, lem:kaplansky_transform_fixed_on_extreme")
Let $`M` have specified predual $`P`, let $`V\subseteq P` be
Sakai-invariant, and let $`A` be a self-adjoint subalgebra dense for
$`\sigma(M,V)`.  Then $`A\cap S_M` is dense in $`S_M` for the Mackey topology
$`\tau(M,P)`.
:::

:::proof "thm:kaplansky_density_Sak_1_9_1"
Taking the norm closure of $`A` preserves the hypotheses and conclusion.  The
transform closure theorem and its fixed-point property show that the
ultraweak closure of $`A\cap S_M` contains every extreme point of $`S_M`.
This closure is convex, and $`S_M` is ultraweakly compact, so Krein--Milman
makes it all of $`S_M`.  Compatible ultraweak and Mackey topologies have the
same closure on the convex set $`A\cap S_M`.
:::

:::corollary "cor:kaplansky_density_ultraweak" (parent := "kaplansky-density") (lean := "Ultraweak.SakaiInvariantTestSpace.kaplansky_density_ultraweak") (uses := "thm:kaplansky_density_Sak_1_9_1, thm:sigma_le_s_le_tau")
If $`A` is a self-adjoint subalgebra ultraweakly dense in a W-star algebra
$`M`, then $`A\cap S_M` is dense in $`S_M` for the Mackey topology, and hence
also for the strong and ultraweak topologies.
:::

:::proof "cor:kaplansky_density_ultraweak"
Take $`V=P`.  The whole predual is Sakai-invariant by ultraweak continuity of
star and fixed multiplication.  Apply the theorem and then
$`\sigma(M,P)\leq s(M,P)\leq\tau(M,P)`.
:::
