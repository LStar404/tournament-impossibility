import RecoveryApproximationOuterRadius

/-! Actual analytic derivatives at z=1, identified with the previously proved
falling-factorial coefficient sums using a genuine outer coefficient radius. -/
noncomputable section
namespace ActualRecoveryDerivativeBridge
open ActualGraphCoreRecovery PermanentNormalizedFrozenBridge
open RecoveryMomentTail WeightedRecoveryClosure FormalSeriesDerivativeAtOne

section Graph
variable {C : Type*} [Fintype C] [DecidableEq C] {n : ℕ}
variable (hn : 24 ≤ n) (d : ℕ)
variable (e : BinaryBalancedTensor.Bits (d+1) ≃ Fin (2^(d+1))) (B : Matrix C C ℝ)
variable (hB : ∀ i j, B j i= -B i j) (he : ∀ i j, |B i j| ≤ 1)
variable (f : Fin n ≃ C × BinaryBalancedTensor.Bits (d+1)) (v : ℝ) (hv : |v| ≤ 1)
include hn hB he hv

/-- The analytic derivative is of the evaluation of the same untruncated U,
not a separately chosen analytic function. -/
theorem approximation_at_one (p ell : ℕ) :
    let M := TournamentSkewMargin.branch (BinaryRawGraphWeighted.realGraph (d+1) e B f) v
    iteratedDeriv ell (FormalSeriesDerivativeAtOne.eval (untruncated M p)) 1=
      fallingFactorialSum (fun k => (untruncated M p).coeff k) ell := by
  exact FormalSeriesDerivativeAtOne.at_one (by norm_num : (1 : ℝ)<17/16) _
    (RecoveryApproximationOuterRadius.graph hn d e B hB he f v hv p) ell

/-- All fixed orders, with the same explicit dimension/window condition and
constant as the proved weighted coefficient error. -/
theorem normalized_derivative_error (p ell : ℕ) (hp : p ≤ degree d n) :
    let M := TournamentSkewMargin.branch (BinaryRawGraphWeighted.realGraph (d+1) e B f) v
    ‖iteratedDeriv ell (normalized M).eval 1-
      iteratedDeriv ell (FormalSeriesDerivativeAtOne.eval (untruncated M p)) 1‖ ≤
        ActualWeightedUntruncatedRecovery.errorConstant d p ell/(n : ℝ)^(p+1) := by
  dsimp only
  rw [FormalSeriesDerivativeAtOne.polynomial_at_one,
    approximation_at_one hn d e B hB he f v hv p ell]
  exact (ActualWeightedUntruncatedRecovery.derivative_coefficients_at_one hn d e B hB he f v hv p ell hp).2

/-- Literal actual permanent derivative at 1 versus the untruncated actual
recovery series. No external analytic-identification premise remains. -/
theorem actual_permanent_derivative_error (p ell : ℕ) (hp : p ≤ degree d n) :
    let M := TournamentSkewMargin.branch (BinaryRawGraphWeighted.realGraph (d+1) e B f) v
    ‖iteratedDeriv ell (fun z : ℂ =>
        Matrix.permanent (fun i j => 1+(n : ℂ)*z*M i j)/(n.factorial : ℂ)) 1-
      iteratedDeriv ell (FormalSeriesDerivativeAtOne.eval (untruncated M p)) 1‖ ≤
        ActualWeightedUntruncatedRecovery.errorConstant d p ell/(n : ℝ)^(p+1) := by
  let M := TournamentSkewMargin.branch (BinaryRawGraphWeighted.realGraph (d+1) e B f) v
  have hf : (fun z : ℂ => Matrix.permanent (fun i j => 1+(n : ℂ)*z*M i j)/(n.factorial : ℂ))=
      (normalized M).eval := by
    funext z
    exact (PermanentNormalizedTailBridge.eval_actual M (by omega) z).symm
  change ‖iteratedDeriv ell (fun z : ℂ => Matrix.permanent (fun i j => 1+(n : ℂ)*z*M i j)/(n.factorial : ℂ)) 1-
    iteratedDeriv ell (FormalSeriesDerivativeAtOne.eval (untruncated M p)) 1‖ ≤ _
  rw [hf]
  exact normalized_derivative_error hn d e B hB he f v hv p ell hp
end Graph
end ActualRecoveryDerivativeBridge
#print axioms ActualRecoveryDerivativeBridge.approximation_at_one
#print axioms ActualRecoveryDerivativeBridge.normalized_derivative_error
#print axioms ActualRecoveryDerivativeBridge.actual_permanent_derivative_error
