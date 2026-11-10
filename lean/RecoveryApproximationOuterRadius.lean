import FormalSeriesDerivativeAtOne
import ActualWeightedUntruncatedRecovery

/-! The same untruncated actual approximation has radius strictly greater than
one, proved from the old 9/8 bounds, not from unit-radius polynomial moments. -/
noncomputable section
namespace RecoveryApproximationOuterRadius
open WeightedCoefficientNorm RecoveryMomentTail
open ActualResidualFrozenFactorization BinaryGraphActivityBound

def majorant (n a : ℕ) (F : PowerSeries ℂ) (k : ℕ) : ℝ :=
  (RecoveryFiniteOrderRemainder.H k a/(n : ℝ)^a)*‖F.coeff k‖*(17/16 : ℝ)^k

lemma majorant_summable (n a : ℕ) (F : PowerSeries ℂ) (hF : Finite (9/8) F) :
    Summable (majorant n a F) := by
  have hm := FormalSeriesDerivativeAtOne.moment_summable
    (by norm_num : (0 : ℝ) ≤ 17/16) (by norm_num : (17/16 : ℝ)<9/8) F hF (2*a)
  have hs := hm.mul_left (1/(n : ℝ)^a)
  apply hs.of_nonneg_of_le
  · intro k
    exact mul_nonneg (mul_nonneg (div_nonneg (H_nonneg k a) (by positivity)) (norm_nonneg _)) (by positivity)
  · intro k
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (H_bound k a) (pow_nonneg (Nat.cast_nonneg n) a))
        (norm_nonneg (F.coeff k))) (show 0 ≤ (17/16 : ℝ)^k by positivity)
    unfold majorant
    convert h using 1 <;> ring

/-- Only the finite family j ≤ p is needed; no infinite activity convergence. -/
theorem finite {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (p : ℕ)
    (hF : ∀ j∈Finset.range (p+1), Finite (9/8) (core M*rawActivity M j)) :
    Finite (17/16) (untruncated M p) := by
  have hs : Summable (fun k => ∑ j∈Finset.range (p+1), ∑ a∈Finset.range (p-j+1),
      majorant n a (core M*rawActivity M j) k) :=
    summable_sum (fun j hj => summable_sum (fun a ha => majorant_summable n a _ (hF j hj)))
  apply hs.of_nonneg_of_le (nonneg (by norm_num) _)
  intro k
  have hm := coefficient_majorant M p 0 k
  simp only [pow_zero, one_mul, mul_one] at hm
  have hh := mul_le_mul_of_nonneg_right hm (show 0 ≤ (17/16 : ℝ)^k by positivity)
  simpa only [mass, majorant, Finset.sum_mul, mul_assoc] using hh

/-- n≥24 suffices for the outer-radius statement. Unlike the error estimate,
this analytic identification does not require p ≤ floor(alpha_d*n). -/
theorem graph {C : Type*} [Fintype C] [DecidableEq C] {n : ℕ}
    (hn : 24 ≤ n) (d : ℕ)
    (e : BinaryBalancedTensor.Bits (d+1) ≃ Fin (2^(d+1))) (B : Matrix C C ℝ)
    (hB : ∀ i j, B j i= -B i j) (he : ∀ i j, |B i j| ≤ 1)
    (f : Fin n ≃ C × BinaryBalancedTensor.Bits (d+1)) (v : ℝ) (hv : |v| ≤ 1) (p : ℕ) :
    let M := TournamentSkewMargin.branch (BinaryRawGraphWeighted.realGraph (d+1) e B f) v
    Finite (17/16) (untruncated M p) := by
  apply finite
  intro j hj
  exact (ActualWeightedUntruncatedRecovery.product_bound_all hn d e B hB he f v hv j).1
end RecoveryApproximationOuterRadius
#print axioms RecoveryApproximationOuterRadius.finite
#print axioms RecoveryApproximationOuterRadius.graph
