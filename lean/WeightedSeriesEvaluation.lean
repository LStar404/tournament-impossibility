import FormalSeriesDerivativeAtOne

/-!
Absolute coefficient convergence gives the Cauchy-product evaluation identity.
No recovery estimate or determinant branch identification is assumed here.
-/
set_option autoImplicit false
noncomputable section
namespace WeightedSeriesEvaluation
open WeightedCoefficientNorm

lemma norm_summable (rho : ℝ) (F : PowerSeries ℂ)
    (hF : Finite rho F) (z : ℂ) (hz : ‖z‖ ≤ rho) :
    Summable (fun k => ‖F.coeff k*z^k‖) := by
  apply hF.of_nonneg_of_le (fun k => norm_nonneg _) 
  intro k
  simp only [norm_mul, norm_pow, mass]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg z) hz k) (norm_nonneg _)

lemma summable (rho : ℝ) (F : PowerSeries ℂ)
    (hF : Finite rho F) (z : ℂ) (hz : ‖z‖ ≤ rho) :
    Summable (fun k => F.coeff k*z^k) :=
  (norm_summable rho F hF z hz).of_norm

/-- Includes the boundary, since finiteness is assumed at rho itself. -/
theorem eval_mul (rho : ℝ) (F G : PowerSeries ℂ)
    (hF : Finite rho F) (hG : Finite rho G)
    (z : ℂ) (hz : ‖z‖ ≤ rho) :
    FormalSeriesDerivativeAtOne.eval (F*G) z =
      FormalSeriesDerivativeAtOne.eval F z * FormalSeriesDerivativeAtOne.eval G z := by
  unfold FormalSeriesDerivativeAtOne.eval
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
    (norm_summable rho F hF z hz) (norm_summable rho G hG z hz)]
  apply tsum_congr
  intro k
  rw [PowerSeries.coeff_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  rw [← he, pow_add]
  ring

lemma eval_add (rho : ℝ) (F G : PowerSeries ℂ)
    (hF : Finite rho F) (hG : Finite rho G)
    (z : ℂ) (hz : ‖z‖ ≤ rho) :
    FormalSeriesDerivativeAtOne.eval (F+G) z =
      FormalSeriesDerivativeAtOne.eval F z + FormalSeriesDerivativeAtOne.eval G z := by
  unfold FormalSeriesDerivativeAtOne.eval
  simp only [map_add, add_mul]
  exact (summable rho F hF z hz).tsum_add (summable rho G hG z hz)

end WeightedSeriesEvaluation
#check @WeightedSeriesEvaluation.norm_summable
#print axioms WeightedSeriesEvaluation.norm_summable
#check @WeightedSeriesEvaluation.summable
#print axioms WeightedSeriesEvaluation.summable
#check @WeightedSeriesEvaluation.eval_mul
#print axioms WeightedSeriesEvaluation.eval_mul
#check @WeightedSeriesEvaluation.eval_add
#print axioms WeightedSeriesEvaluation.eval_add
