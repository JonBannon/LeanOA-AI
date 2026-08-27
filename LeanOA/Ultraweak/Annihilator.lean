module

public import LeanOA.Mathlib.RingTheory.Annihilator
public import LeanOA.Ultraweak.Multiplication
public import LeanOA.Ultraweak.Opposite

@[expose] public section

/-!
# Ultraweak closedness of annihilators

Algebraic annihilators are ultraweakly closed because they are intersections of kernels of
continuous fixed-multiplication maps.
-/

open Set
open scoped Ultraweak

variable {M P : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] [Predual ℂ M P]

namespace Ideal

/-- The left annihilator of any set in a C-star algebra is ultraweakly closed. -/
theorem isClosed_leftAnnihilator (s : Set M) :
    IsClosed (Ultraweak.ofSubmodule (P := P)
      ((leftAnnihilator s).restrictScalars ℂ) : Set σ(M, P)) := by
  rw [show (Ultraweak.ofSubmodule (P := P)
      ((leftAnnihilator s).restrictScalars ℂ) : Set σ(M, P)) =
      ⋂ a : s, Ultraweak.mulRightL (P := P) a.1 ⁻¹' {0} by
    ext x
    simp only [SetLike.mem_coe, Ultraweak.mem_ofSubmodule, Submodule.restrictScalars_mem,
      mem_leftAnnihilator, iInter_coe_set, mem_iInter, mem_preimage,
      Ultraweak.mulRightL_apply, Ultraweak.toUltraweak_mul, toUltraweak_ofUltraweak,
      mem_singleton_iff]
    constructor
    · intro h a ha
      simpa only [Ultraweak.toUltraweak_mul, toUltraweak_ofUltraweak,
        toUltraweak_zero] using congr_arg (toUltraweak ℂ P) (h a ha)
    · intro h a ha
      simpa only [Ultraweak.ofUltraweak_mul, ofUltraweak_toUltraweak,
        ofUltraweak_zero] using congr_arg (ofUltraweak (M := M) (P := P)) (h a ha)]
  exact isClosed_iInter fun a ↦
    isClosed_singleton.preimage (Ultraweak.mulRightL (P := P) a.1).continuous

/-- The right annihilator of any set in a C-star algebra, represented in the opposite algebra, is
ultraweakly closed. -/
theorem isClosed_rightAnnihilator (s : Set M) :
    IsClosed (Ultraweak.ofSubmodule (P := P)
      ((rightAnnihilator s).restrictScalars ℂ) : Set σ(Mᵐᵒᵖ, P)) := by
  rw [rightAnnihilator_eq_leftAnnihilator_image_op]
  exact isClosed_leftAnnihilator (M := Mᵐᵒᵖ) (P := P) (MulOpposite.op '' s)

end Ideal

namespace TwoSidedIdeal

/-- The two-sided annihilator of a left ideal is ultraweakly closed. -/
theorem isClosed_annihilatorOfIdeal (I : Ideal M) :
    IsClosed (Ultraweak.ofSubmodule (P := P)
      ((annihilatorOfIdeal I).asIdeal.restrictScalars ℂ) : Set σ(M, P)) := by
  rw [asIdeal_annihilatorOfIdeal]
  exact Ideal.isClosed_leftAnnihilator (P := P) (I : Set M)

/-- The two-sided annihilator of a right ideal, encoded in the opposite algebra, is ultraweakly
closed. -/
theorem isClosed_annihilatorOfIdealOpposite (I : Ideal Mᵐᵒᵖ) :
    IsClosed (Ultraweak.ofSubmodule (P := P)
      ((annihilatorOfIdealOpposite I).asIdeal.restrictScalars ℂ) : Set σ(M, P)) := by
  rw [show (Ultraweak.ofSubmodule (P := P)
      ((annihilatorOfIdealOpposite I).asIdeal.restrictScalars ℂ) : Set σ(M, P)) =
      ⋂ y : I, Ultraweak.mulLeftL (P := P) y.1.unop ⁻¹' {0} by
    ext x
    simp only [SetLike.mem_coe, Ultraweak.mem_ofSubmodule, Submodule.restrictScalars_mem,
      mem_asIdeal, mem_annihilatorOfIdealOpposite, MulOpposite.forall,
      MulOpposite.unop_op, mem_iInter, mem_preimage, Ultraweak.mulLeftL_apply,
      Ultraweak.toUltraweak_mul, toUltraweak_ofUltraweak, mem_singleton_iff,
      Subtype.forall]
    constructor
    · intro h a ha
      simpa only [Ultraweak.toUltraweak_mul, toUltraweak_ofUltraweak,
        toUltraweak_zero] using congr_arg (toUltraweak ℂ P) (h a ha)
    · intro h a ha
      simpa only [Ultraweak.ofUltraweak_mul, ofUltraweak_toUltraweak,
        ofUltraweak_zero] using congr_arg (ofUltraweak (M := M) (P := P)) (h a ha)]
  exact isClosed_iInter fun y ↦
    isClosed_singleton.preimage (Ultraweak.mulLeftL (P := P) y.1.unop).continuous

end TwoSidedIdeal
