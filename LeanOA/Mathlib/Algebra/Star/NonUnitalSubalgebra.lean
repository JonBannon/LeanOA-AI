module

public import LeanOA.IsUnital
public import Mathlib.Algebra.Star.NonUnitalSubalgebra
public import Mathlib.Algebra.Star.StarProjection

@[expose] public section

/-!
# Internally unital star-closed submagmas

This file contains algebraic results about star-closed multiplicative subobjects which are not
presently available in Mathlib.
-/

namespace IsUnital

variable {A S : Type*} [Mul A] [StarMul A] [SetLike S A]
  [MulMemClass S A] [StarMemClass S A]

/-- The ambient value of the internal unit of a star-closed submagma is a star projection.

This requires no associativity, additive structure, scalar action, norm, or topology. -/
theorem isStarProjection_coe_unit (s : S) [IsUnital s] :
    IsStarProjection ((isUnital.choose : s) : A) := by
  let e : s := isUnital.choose
  have he (x : s) := isUnital.choose_spec x
  refine ⟨congr_arg Subtype.val (he e).1, ?_⟩
  have hstar : star e = e := (he (star e)).2.symm.trans <| by
    simpa only [star_mul, star_star] using congr_arg star (he (star e)).2
  exact congr_arg Subtype.val hstar

end IsUnital
