module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Extended operator energy along a Hilbert basis

This file defines the possibly infinite sum

`sum' i, enorm (T (b i)) ^ 2`

for a continuous linear map `T` and an arbitrary-index Hilbert basis `b`.  Parseval's identity and
Tonelli interchange identify this energy with the corresponding energy of the adjoint.  It follows
that the value is independent of the chosen domain Hilbert basis.

The value lies in `ENNReal`: no summability or separability hypothesis is hidden, and divergent
energy is represented by `infinity`.  This is representation-neutral infrastructure; it does not
define a Hilbert--Schmidt or trace-class carrier.
-/

@[expose] public section

open scoped ENNReal InnerProductSpace

noncomputable section

namespace HilbertBasis

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {ι : Type*}

/-- Parseval's identity as a `HasSum` statement for the squared norms of the coefficients of an
arbitrary-index Hilbert basis. -/
protected theorem hasSum_sq_norm_inner_right (b : HilbertBasis ι 𝕜 E) (x : E) :
    HasSum (fun i ↦ ‖⟪b i, x⟫_𝕜‖ ^ 2) (‖x‖ ^ 2) := by
  have h : HasSum (fun i ↦ ‖⟪b i, x⟫_𝕜‖ ^ 2) (RCLike.re ⟪x, x⟫_𝕜) := by
    refine HasSum.congr_fun
      (RCLike.hasSum_re 𝕜 (b.hasSum_inner_mul_inner x x)) (fun i ↦ ?_)
    rw [← inner_conj_symm x (b i), RCLike.conj_mul,
      ← RCLike.ofReal_pow, RCLike.ofReal_re]
  simpa only [inner_self_eq_norm_sq] using h

/-- Extended-nonnegative-real Parseval identity.  Unlike a real-valued `tsum`, this statement
retains the correct value even when it is later used inside a possibly divergent outer sum. -/
protected theorem tsum_sq_enorm_inner_right (b : HilbertBasis ι 𝕜 E) (x : E) :
    ∑' i, ‖⟪b i, x⟫_𝕜‖ₑ ^ 2 = ‖x‖ₑ ^ 2 := by
  simp_rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _) 2]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i ↦ sq_nonneg _)
    (b.hasSum_sq_norm_inner_right x).summable,
    (b.hasSum_sq_norm_inner_right x).tsum_eq]

section OperatorEnergy

variable {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The extended Hilbert-basis energy of a continuous linear map.  The value is `infinity` when
the family of squared norms is not summable. -/
def operatorEnergy (b : HilbertBasis ι 𝕜 E) (T : E →L[𝕜] F) : ℝ≥0∞ :=
  ∑' i, ‖T (b i)‖ₑ ^ 2

@[simp]
theorem operatorEnergy_zero (b : HilbertBasis ι 𝕜 E) :
    b.operatorEnergy (0 : E →L[𝕜] F) = 0 := by
  simp [operatorEnergy, ← ofReal_norm]

/-- Finite extended operator energy is exactly ordinary square summability along the basis. -/
theorem operatorEnergy_ne_top_iff_summable_norm_sq
    (b : HilbertBasis ι 𝕜 E) (T : E →L[𝕜] F) :
    b.operatorEnergy T ≠ ∞ ↔ Summable (fun i ↦ ‖T (b i)‖ ^ 2) := by
  change (∑' i, ((‖T (b i)‖₊ ^ 2 : NNReal) : ℝ≥0∞)) ≠ ∞ ↔ _
  rw [ENNReal.tsum_coe_ne_top_iff_summable_coe]
  simp only [NNReal.coe_pow, coe_nnnorm]

end OperatorEnergy

section Adjoint

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  {κ : Type*}

/-- Operators that form an adjoint pair have equal extended energies along arbitrary Hilbert
bases.  This is the completeness-free core of `operatorEnergy_eq_adjoint`. -/
theorem operatorEnergy_eq_of_isAdjointPair
    (e : HilbertBasis ι 𝕜 E) (f : HilbertBasis κ 𝕜 F)
    (T : E →L[𝕜] F) (S : F →L[𝕜] E)
    (hTS : LinearMap.IsAdjointPair
      (LinearMap.flip (innerₛₗ 𝕜 (E := E)))
      (LinearMap.flip (innerₛₗ 𝕜 (E := F))) T S) :
    e.operatorEnergy T = f.operatorEnergy S := by
  calc
    ∑' i, ‖T (e i)‖ₑ ^ 2 = ∑' i, ∑' j, ‖⟪f j, T (e i)⟫_𝕜‖ₑ ^ 2 := by
      apply tsum_congr
      intro i
      exact (f.tsum_sq_enorm_inner_right (T (e i))).symm
    _ = ∑' j, ∑' i, ‖⟪f j, T (e i)⟫_𝕜‖ₑ ^ 2 := ENNReal.tsum_comm
    _ = ∑' j, ‖S (f j)‖ₑ ^ 2 := by
      apply tsum_congr
      intro j
      rw [← e.tsum_sq_enorm_inner_right (S (f j))]
      apply tsum_congr
      intro i
      congr 1
      rw [← ofReal_norm, ← ofReal_norm]
      have h : ⟪f j, T (e i)⟫_𝕜 = ⟪S (f j), e i⟫_𝕜 := by
        simpa only [LinearMap.flip_apply, innerₛₗ_apply_apply] using hTS (e i) (f j)
      congr 1
      calc
        ‖⟪f j, T (e i)⟫_𝕜‖ = ‖⟪S (f j), e i⟫_𝕜‖ := congrArg norm h
        _ = ‖⟪e i, S (f j)⟫_𝕜‖ := norm_inner_symm _ _

variable [CompleteSpace E] [CompleteSpace F]

/-- The extended energy of an operator along a domain basis equals the extended energy of its
adjoint along a codomain basis.  Both basis index types are arbitrary. -/
theorem operatorEnergy_eq_adjoint
    (e : HilbertBasis ι 𝕜 E) (f : HilbertBasis κ 𝕜 F) (T : E →L[𝕜] F) :
    e.operatorEnergy T = f.operatorEnergy T.adjoint :=
  e.operatorEnergy_eq_of_isAdjointPair f T T.adjoint T.isAdjointPair_inner

/-- Extended operator energy is independent of the chosen Hilbert basis of the domain. -/
theorem operatorEnergy_basis_independent
    (e₁ : HilbertBasis ι 𝕜 E) (e₂ : HilbertBasis κ 𝕜 E) (T : E →L[𝕜] F) :
    e₁.operatorEnergy T = e₂.operatorEnergy T := by
  obtain ⟨w, f, -⟩ := exists_hilbertBasis 𝕜 F
  calc
    e₁.operatorEnergy T = f.operatorEnergy T.adjoint := e₁.operatorEnergy_eq_adjoint f T
    _ = e₂.operatorEnergy T := (e₂.operatorEnergy_eq_adjoint f T).symm

end Adjoint

end HilbertBasis
