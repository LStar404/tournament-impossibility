import PositiveBranchEvaluationCandidate
import GeneralBalancedWeighted
import Mathlib.LinearAlgebra.Matrix.SchurComplement
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace ActualBalancedCoreDeterminantCandidate
open Matrix BalancedRawData GeneralBalancedWeighted
open AffineDeterminantEvaluationCandidate PositiveBranchEvaluationCandidate
open scoped Matrix.Norms.L2Operator
variable {m : ℕ}
local instance sumDecidable (m : ℕ) : DecidableEq (Fin m ⊕ Fin m) := Classical.typeDecidableEq _
lemma actual_complexify (M : Matrix (Fin m) (Fin m) ℝ) :
    complexify (realBlock M)=block M := by
  exact cast_realBlock M
lemma actual_schur (M : Matrix (Fin m) (Fin m) ℝ) :
    (1+realBlock M).det=
      (1-(M-ActualHessianFinite.P m)ᵀ*(M-ActualHessianFinite.P m)).det := by
  have he : 1+realBlock M=Matrix.fromBlocks 1 (M-ActualHessianFinite.P m)
      (M-ActualHessianFinite.P m)ᵀ 1 := by
    apply Matrix.ext
    intro i j
    change (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ) i j + realBlock M i j = _
    cases i <;> cases j <;>
      simp [realBlock,FullWickSquarefreeCompatibility.block,FinitePairingPermanent.covariance,
        Matrix.one_apply,Matrix.fromBlocks]
  rw [he]
  have hdet : @Matrix.det (Fin m ⊕ Fin m) (sumDecidable m) _ ℝ _ (Matrix.fromBlocks 1 (M-ActualHessianFinite.P m) (M-ActualHessianFinite.P m)ᵀ 1) =
      @Matrix.det (Fin m ⊕ Fin m) (fun a b => instDecidableEqSum a b) _ ℝ _ (Matrix.fromBlocks 1 (M-ActualHessianFinite.P m) (M-ActualHessianFinite.P m)ᵀ 1) := by
    congr 1
  exact hdet.trans (Matrix.det_fromBlocks_one₁₁ _ _ _)
lemma actual_core_square (hm : 0 < m) (M : Matrix (Fin m) (Fin m) ℝ)
    (hr : ∀ i,(∑ j,M i j)=1) (hc : ∀ j,(∑ i,M i j)=1) :
    (ActualResidualFrozenFactorization.core (centeredComplex M))^2*
      (affineSeries (complexify (realBlock M))).det=1 := by
  rw [actual_complexify,actual_core_eq_branch hm M hr hc,←mixed_affine]
  exact NormalizedDeterminantBranch.branch_square _ (MixedEvenMatrix.constant_det _ _)
/-- Exact positive-real branch of the actual core, with no external series,
formal-square, determinant-positivity or root-choice assumptions. -/
theorem actual_core_determinant (hm : 0 < m) (M : Matrix (Fin m) (Fin m) ℝ)
    (C q : ℝ) (hC : 0≤C) (hM : ∀ i j,0≤M i j)
    (hd : ∀ i j,M i j≤C/(m:ℝ))
    (hr : ∀ i,(∑ j,M i j)=1) (hc : ∀ j,(∑ i,M i j)=1)
    (hq0 : 0≤q) (hq1 : q<1)
    (hN : ‖Matrix.toEuclideanCLM (𝕜:=ℝ) (M-ActualHessianFinite.P m)‖≤q) :
    FormalSeriesDerivativeAtOne.eval (ActualResidualFrozenFactorization.core
      (ActualHessianComplex.realComplex (M-ActualHessianFinite.P m))) 1=
      ((Real.sqrt (1-(M-ActualHessianFinite.P m)ᵀ*(M-ActualHessianFinite.P m)).det)⁻¹:ℝ) := by
  have hh := actual_uniform_bounds hm M C q hC hM hd hr hc hq0 hq1 hN
  have hQ : ‖realBlock M‖<1 := by
    have hhq := (real_block_norm M hq0 hN).trans_lt hq1
    have heq : Classical.typeDecidableEq (Fin m ⊕ Fin m) = (fun a b => instDecidableEqSum a b) := Subsingleton.elim _ _
    simpa (config := { instances := true }) only [sumDecidable, heq, Matrix.l2_opNorm_toEuclideanCLM] using hhq
  have hp := positive_sqrt_endpoint (realBlock M) hQ
    (ActualResidualFrozenFactorization.core (centeredComplex M)) hh.1 hh.2.1.1
    (actual_core_square hm M hr hc) (ActualResidualFrozenFactorization.core_constant _)
  rw [actual_schur] at hp
  exact hp
end ActualBalancedCoreDeterminantCandidate
#print axioms ActualBalancedCoreDeterminantCandidate.actual_complexify
#check ActualBalancedCoreDeterminantCandidate.actual_complexify
#print axioms ActualBalancedCoreDeterminantCandidate.actual_schur
#check ActualBalancedCoreDeterminantCandidate.actual_schur
#print axioms ActualBalancedCoreDeterminantCandidate.actual_core_square
#check ActualBalancedCoreDeterminantCandidate.actual_core_square
#print axioms ActualBalancedCoreDeterminantCandidate.actual_core_determinant
#check ActualBalancedCoreDeterminantCandidate.actual_core_determinant
