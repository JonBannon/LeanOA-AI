import Verso
import VersoManual
import VersoBlueprint
import LeanOA

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Positive functionals and separation" =>

Let $`M` be a W-star algebra, $`M_+` its positive cone, and $`T` the
ultraweakly continuous positive complex-linear functionals.  This chapter
establishes the closed-cone and separation facts used in monotone convergence
and normality.

The legacy source also recorded, only as a commented future proposal, the
state-space formula
$`\lVert h\rVert=\sup_\varphi|\varphi(h)|` for self-adjoint $`h`.  It had no
active blueprint node or linked Lean declaration, so it remains future work
rather than being misreported as completed in the graph.

{index}[positive functional]
{index}[positive cone]
{index}[separation]

:::lemma_ "lem:pos_cvx_cone" (lean := "ConvexCone.positive") (tags := "mathlib")
The positive cone $`M_+` is a convex cone.
:::

:::proof "lem:pos_cvx_cone"
Closure under addition and multiplication by nonnegative real scalars is the
standard ordered-star-ring API packaged by `ConvexCone.positive`.
:::

:::lemma_ "lem:pos_sa_sigma_closed_Sak_1_7_1" (lean := "Ultraweak.isClosed_setOf_isSelfAdjoint, Ultraweak.isClosed_nonneg") (uses := "def:sigma_top")
The positive cone and the set of self-adjoint elements are ultraweakly closed.
:::

:::proof "lem:pos_sa_sigma_closed_Sak_1_7_1"
Self-adjointness is the equalizer of the identity and the ultraweakly
continuous star map.  Positivity is recovered from inequalities against
ultraweakly continuous positive functionals, hence is an intersection of
closed half-spaces.
:::

:::lemma_ "lem:non_pos_elem_neg_for_some_state_Sak_1_7_2" (lean := "Ultraweak.exists_positiveCLM_apply_lt_zero") (uses := "def:sigma_top, lem:pos_cvx_cone, lem:pos_sa_sigma_closed_Sak_1_7_1")
If a self-adjoint element $`a` is not positive, there is an ultraweakly
continuous positive functional $`\varphi` with $`\varphi(a)<0`.
:::

:::proof "lem:non_pos_elem_neg_for_some_state_Sak_1_7_2"
Apply geometric Hahn--Banach separation to the ultraweakly closed convex cone
$`M_+` in the underlying real locally convex space.  The cone property makes
the separator nonnegative on $`M_+`.  Symmetrize it with the ultraweakly
continuous star operation and extend complex-linearly; on self-adjoint
elements it retains the separating value.
:::

:::lemma_ "lem:uw_pos_sep_pts" (lean := "Ultraweak.ext_positiveCLM") (uses := "lem:non_pos_elem_neg_for_some_state_Sak_1_7_2, def:sigma_top")
If every ultraweakly continuous positive functional vanishes at $`a\in M`,
then $`a=0`.
:::

:::proof "lem:uw_pos_sep_pts"
For self-adjoint $`a`, apply positive separation to $`a` and $`-a` to obtain
$`a\geq0` and $`a\leq0`.  For arbitrary $`a`, positive functionals preserve
star and therefore vanish on its real and imaginary self-adjoint parts; the
self-adjoint case makes both parts zero.
:::
