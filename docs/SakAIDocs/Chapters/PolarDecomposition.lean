import Verso
import VersoManual
import VersoBlueprint
import LeanOA.Ultraweak.ElementPolarDecomposition

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Element polar decomposition" =>

This chapter completes Sakai's Section 1.12.  It constructs the polar factor
of an arbitrary element of a $`W^*`-algebra and characterizes that factor by
its initial and final support projections.

{index}[polar decomposition]
{index}[partial isometry]
{index}[absolute value]

:::group "element-polar-decomposition"
Absolute values and the polar decomposition of elements.
:::

# Absolute value and polar factor
%%%
tag := "element-polar-decomposition"
%%%

:::definition "def:cfc_absolute_value" (parent := "element-polar-decomposition") (lean := "CFC.abs, CFC.abs_nonneg, CFC.abs_mul_abs") (uses := "def:cstar_def") (tags := "mathlib")
For an element $`a` of a $`C^*`-algebra, its absolute value is the
nonnegative self-adjoint element
$`|a|=(a^*a)^{1/2}` supplied by the continuous functional calculus.  It
satisfies $`|a||a|=a^*a`.
:::

:::theorem "thm:element_polar_decomposition_Sak_1_12_1" (parent := "element-polar-decomposition") (lean := "WStarAlgebra.existsUnique_element_polar_decomposition") (uses := "def:cfc_absolute_value, thm:Banach_Alaoglu, lem:star_left_mul_right_mul_sig_cts_Sak_1_7_8, prop:left_right_support_characterization, lem:support_star_compatibility")
Let $`M` be a $`W^*`-algebra and let $`a\in M`.  There is a unique
$`u\in M` such that

* $`a=u|a|`;
* $`u^*u=s(|a|)`;
* $`uu^*=s(|a^*|)`.

Thus $`u` is the polar factor of $`a`, with precisely the displayed initial
and final projections; in particular, it is a partial isometry.  This is
Sakai's Theorem 1.12.1.
:::

:::proof "thm:element_polar_decomposition_Sak_1_12_1"
Sakai's regularizers give contractions $`b_n` and positive invertible
$`h_n` such that $`b_nh_n=a` and $`h_n\to|a|` in norm.  Ultraweak
compactness of the closed unit ball gives a cluster point $`b`; continuity
of multiplication by the fixed element $`|a|` then yields $`b|a|=a`.

Put $`p=s(|a|)`, $`q=s(|a^*|)`, and $`u=qbp`.  Contractivity and a positive
square-root argument show that the initial-support defect
$`p-u^*u` annihilates $`|a|`.  The support zero-kernel property therefore
gives $`u^*u=p`.  Since $`qu=u`, one has $`uu^*\leq q`; conversely,
$`uu^*` fixes $`a`, so minimality of the left support gives
$`q\leq uu^*`.  This identifies the final projection directly; Sakai's
corresponding computation passes through the identity
$`aa^*=u(a^*a)u^*`.

For uniqueness, suppose $`v` satisfies the same factorization and
initial-support equation.  Then $`(u-v)|a|=0`, hence
$`(u-v)p=0`.  The equations $`u^*u=p=v^*v` imply $`up=u` and $`vp=v`, so
$`u=v`.  In particular, the final-support equation is part of the exact
source characterization but is not needed for the algebraic uniqueness
argument.
:::
