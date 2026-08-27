module

public import Mathlib.RingTheory.TwoSidedIdeal.Operations

@[expose] public section

/-!
# One-sided annihilators in noncommutative rings

This file defines left and right annihilators using Mathlib's one-sided `Ideal`, representing right
ideals of `R` as left ideals of `Rᵐᵒᵖ`. It also packages the annihilator of a one-sided ideal
as Mathlib's native `TwoSidedIdeal` at the ring boundary required by that structure.
-/

namespace Ideal

variable {R : Type*} [Semiring R]

/-- The left annihilator of a set in a semiring, as a left ideal. -/
def leftAnnihilator (s : Set R) : Ideal R :=
  ⨅ a : s, LinearMap.ker (LinearMap.mulRight R a.1)

@[simp]
theorem mem_leftAnnihilator {s : Set R} {x : R} :
    x ∈ leftAnnihilator s ↔ ∀ a ∈ s, x * a = 0 := by
  simp [leftAnnihilator]

/-- The right annihilator of a set in a semiring, represented as a left ideal of the opposite
semiring. -/
def rightAnnihilator (s : Set R) : Ideal Rᵐᵒᵖ :=
  ⨅ a : s, LinearMap.ker (LinearMap.mulRight Rᵐᵒᵖ (MulOpposite.op a.1))

@[simp]
theorem mem_rightAnnihilator {s : Set R} {x : Rᵐᵒᵖ} :
    x ∈ rightAnnihilator s ↔ ∀ a ∈ s, a * x.unop = 0 := by
  simp only [rightAnnihilator, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.mulRight_apply, Subtype.forall]
  constructor
  · intro h a ha
    simpa only [MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.unop_zero] using
      congr_arg MulOpposite.unop (h a ha)
  · intro h a ha
    apply MulOpposite.unop_injective
    simpa only [MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.unop_zero] using h a ha

theorem leftAnnihilator_singleton (a : R) :
    leftAnnihilator {a} = LinearMap.ker (LinearMap.mulRight R a) := by
  ext
  simp

theorem rightAnnihilator_singleton (a : R) :
    rightAnnihilator {a} =
      LinearMap.ker (LinearMap.mulRight Rᵐᵒᵖ (MulOpposite.op a)) := by
  ext x
  rw [mem_rightAnnihilator, LinearMap.mem_ker]
  constructor
  · intro h
    apply MulOpposite.unop_injective
    simpa only [LinearMap.mulRight_apply, MulOpposite.unop_mul, MulOpposite.unop_op,
      MulOpposite.unop_zero] using h a (Set.mem_singleton a)
  · intro h b hb
    rw [Set.mem_singleton_iff.mp hb]
    simpa only [LinearMap.mulRight_apply, MulOpposite.unop_mul, MulOpposite.unop_op,
      MulOpposite.unop_zero] using congr_arg MulOpposite.unop h

/-- A right annihilator is the left annihilator of the image in the opposite semiring. -/
theorem rightAnnihilator_eq_leftAnnihilator_image_op (s : Set R) :
    rightAnnihilator s = leftAnnihilator (MulOpposite.op '' s) := by
  ext x
  rw [mem_rightAnnihilator, mem_leftAnnihilator]
  constructor
  · intro h y hy
    obtain ⟨a, ha, rfl⟩ := hy
    apply MulOpposite.unop_injective
    simpa only [MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.unop_zero] using h a ha
  · intro h a ha
    simpa only [MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.unop_zero] using
      congr_arg MulOpposite.unop (h (MulOpposite.op a) ⟨a, ha, rfl⟩)

end Ideal

namespace TwoSidedIdeal

variable {R : Type*} [Ring R]

/-- The annihilator of a left ideal, as a native two-sided ideal. -/
def annihilatorOfIdeal (I : Ideal R) : TwoSidedIdeal R :=
  mk' {x | ∀ y ∈ I, x * y = 0}
    (by simp)
    (by
      intro x y hx hy z hz
      rw [add_mul, hx z hz, hy z hz, add_zero])
    (by
      intro x hx y hy
      rw [neg_mul, hx y hy, neg_zero])
    (by
      intro x y hy z hz
      rw [mul_assoc, hy z hz, mul_zero])
    (by
      intro x y hx z hz
      rw [mul_assoc, hx (y * z) (I.mul_mem_left y hz)])

@[simp]
theorem mem_annihilatorOfIdeal {I : Ideal R} {x : R} :
    x ∈ annihilatorOfIdeal I ↔ ∀ y ∈ I, x * y = 0 := by
  simp [annihilatorOfIdeal]

/-- The annihilator of a right ideal, represented as an ideal of the opposite ring, as a native
two-sided ideal. -/
def annihilatorOfIdealOpposite (I : Ideal Rᵐᵒᵖ) : TwoSidedIdeal R :=
  (annihilatorOfIdeal I).unop

@[simp]
theorem mem_annihilatorOfIdealOpposite {I : Ideal Rᵐᵒᵖ} {x : R} :
    x ∈ annihilatorOfIdealOpposite I ↔ ∀ y ∈ I, y.unop * x = 0 := by
  rw [annihilatorOfIdealOpposite, mem_unop_iff, mem_annihilatorOfIdeal]
  constructor
  · intro h y hy
    simpa only [MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.unop_zero] using
      congr_arg MulOpposite.unop (h y hy)
  · intro h y hy
    apply MulOpposite.unop_injective
    simpa only [MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.unop_zero] using h y hy

@[simp]
theorem asIdeal_annihilatorOfIdeal (I : Ideal R) :
    (annihilatorOfIdeal I).asIdeal = Ideal.leftAnnihilator (I : Set R) := by
  ext
  simp

@[simp]
theorem asIdealOpposite_annihilatorOfIdealOpposite (I : Ideal Rᵐᵒᵖ) :
    (annihilatorOfIdealOpposite I).asIdealOpposite =
      Ideal.leftAnnihilator (I : Set Rᵐᵒᵖ) := by
  ext x
  rw [mem_asIdealOpposite, mem_annihilatorOfIdealOpposite, Ideal.mem_leftAnnihilator]
  constructor
  · intro h y hy
    apply MulOpposite.unop_injective
    simpa only [MulOpposite.unop_mul, MulOpposite.unop_zero] using h y hy
  · intro h y hy
    simpa only [MulOpposite.unop_mul, MulOpposite.unop_zero] using
      congr_arg MulOpposite.unop (h y hy)

end TwoSidedIdeal
