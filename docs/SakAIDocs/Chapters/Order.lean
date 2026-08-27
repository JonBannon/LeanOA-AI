import Verso
import VersoManual
import VersoBlueprint
import LeanOA

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Order lemmas" =>

Let $`A` be a unital C-star algebra.  Its self-adjoint order is determined by
the positive cone: $`b\leq a` means $`a-b\geq0`.  The following small API is
used repeatedly in the projection and positive-functional developments.

{index}[positive element]
{index}[star conjugation]

:::lemma_ "lem:pos_iff_star_mul_self_Sak_1_4_4" (lean := "CStarAlgebra.nonneg_TFAE, StarOrderedRing.nonneg_iff")
For $`h\in A`, the following are equivalent: $`h\geq0`, and there exists
$`x\in A` such that $`h=x^*x`.
:::

:::proof "lem:pos_iff_star_mul_self_Sak_1_4_4"
This is the square-root characterization of positivity supplied by continuous
functional calculus and exposed through Mathlib's star-ordered-ring API.
:::

:::corollary "lem:star_conj_pos" (lean := "star_left_conjugate_nonneg") (uses := "lem:pos_iff_star_mul_self_Sak_1_4_4") (tags := "mathlib")
If $`h\geq0`, then $`a^*ha\geq0` for every $`a\in A`.
:::

:::proof "lem:star_conj_pos"
Write $`h=x^*x`.  Then $`a^*ha=(xa)^*(xa)`, which is nonnegative.
:::

:::lemma_ "lem:selfadjoint_le_norm" (lean := "IsSelfAdjoint.le_algebraMap_norm_self") (tags := "mathlib")
If $`x\in A` is self-adjoint, then $`x\leq\lVert x\rVert 1`, equivalently
$`\lVert x\rVert1-x\geq0`.
:::

:::proof "lem:selfadjoint_le_norm"
Continuous functional calculus bounds the real spectrum of a self-adjoint
element by its norm, which is exactly the displayed order inequality.
:::
