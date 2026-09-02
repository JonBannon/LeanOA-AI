module

public import LeanOA.Ultraweak.NonUnitalStarSubalgebra
public import LeanOA.Ultraweak.Strong

/-!
# Intrinsic strong topology on an ultraweakly closed subalgebra

This file equips an ultraweakly closed nonunital star subalgebra of an arbitrary dual
C-star-algebra with the intrinsic strong topology determined by its quotient predual. The
construction is independent of any concrete Hilbert-space representation.

All C-star-algebra, unit, spectral-order, and quotient-predual instances remain local to the
type abbreviation. In particular, this file introduces no global instance that could compete
with a different chosen predual.
-/

@[expose] public section

open scoped ComplexOrder Ultraweak

noncomputable section

namespace NonUnitalStarSubalgebra

variable {A Q : Type*} [CStarAlgebra A]
  [NormedAddCommGroup Q] [NormedSpace ℂ Q] [Predual ℂ A Q]

/-- The intrinsic strong topology on an ultraweakly closed self-adjoint subalgebra, formed from
its quotient predual. -/
noncomputable abbrev InducedStrong (S : NonUnitalStarSubalgebra ℂ A)
    (hS : S.IsUltraweakClosed (P := Q)) :=
  letI : NonUnitalCStarAlgebra S := hS.nonUnitalCStarAlgebra S
  letI : IsUnital S := hS.isUnital S
  letI : CStarAlgebra S := IsUnital.toCStarAlgebra
  letI : PartialOrder S := CStarAlgebra.spectralOrder S
  letI : StarOrderedRing S := CStarAlgebra.spectralOrderedRing S
  letI : Predual ℂ S (Q ⧸ Ultraweak.preannihilator (P := Q) S.toSubmodule) :=
    hS.inducedPredual S
  Ultraweak.Strong S (Q ⧸ Ultraweak.preannihilator (P := Q) S.toSubmodule)

/-- A zero-centered norm-closed ball in the intrinsic strong topology of an ultraweakly closed
self-adjoint subalgebra. -/
abbrev InducedStrongClosedBall (S : NonUnitalStarSubalgebra ℂ A)
    (hS : S.IsUltraweakClosed (P := Q)) (r : ℝ) :=
  {T : InducedStrong S hS // ‖(show S from T)‖ ≤ r}

end NonUnitalStarSubalgebra
