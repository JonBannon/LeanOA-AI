module

public import LeanOA.Ultraweak.KaplanskyDensity

/-!
# Restricting the test space of an ultraweak topology

A submodule of a specified predual induces a weaker test topology on the dual algebra.  This file
exposes the canonical continuous identity from the full ultraweak topology to that restricted
weak topology, together with its closed-set consequence.  The underlying general restriction map
for `WeakBilin` lives in the Mathlib-shaped weak-bilinear module.
-/

@[expose] public section

open scoped Ultraweak

noncomputable section

namespace Ultraweak

variable {M P : Type*} [CStarAlgebra M]
  [NormedAddCommGroup P] [NormedSpace ℂ P] [Predual ℂ M P]

/-- The canonical continuous linear identity from the full specified-predual topology to the weak
topology induced by a chosen predual test submodule. -/
def toTestWeakL (V : Submodule ℂ P) :
    σ(M, P) →L[ℂ] WeakBilin (testPairing (M := M) V) :=
  WeakBilin.restrictRightL
    (topDualPairing ℂ P ∘ₗ
      (Predual.equivDual (M := M) |>.toLinearEquiv.toLinearMap)) V.subtype

lemma toTestWeakL_apply (V : Submodule ℂ P) (x : σ(M, P)) :
    WeakBilin.linearEquiv ℂ (testPairing (M := M) V) (toTestWeakL V x) =
      ofUltraweak x :=
  rfl

/-- A set closed for a restricted predual-test topology is closed for the full specified-predual
topology. -/
theorem isClosed_ultraweak_of_isClosed_testWeak (V : Submodule ℂ P) (S : Set M)
    (hS : IsClosed
      ((WeakBilin.linearEquiv ℂ (testPairing (M := M) V)) ⁻¹' S)) :
    IsClosed (ofUltraweak ⁻¹' S : Set σ(M, P)) := by
  convert hS.preimage (toTestWeakL (M := M) (P := P) V).continuous using 1
  ext x
  change ofUltraweak x ∈ S ↔
    WeakBilin.linearEquiv ℂ (testPairing (M := M) V) (toTestWeakL V x) ∈ S
  simp only [toTestWeakL_apply]

end Ultraweak
