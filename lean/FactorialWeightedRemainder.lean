import RecoveryFiniteOrderRemainder
import WeightedPolynomialMultiplier
noncomputable section
namespace FactorialWeightedRemainder
open FiniteFactorialRecovery RecoveryFiniteOrderRemainder WeightedCoefficientNorm

theorem bound (n p : ℕ) (hn : 0<n) (F : PowerSeries ℂ) (E : Finset ℕ)
    (r s sigma : ℝ) (hr : 0 ≤ r) (hs : 0<s) (hsigma : 1<sigma)
    (hgap : sigma*r<s) (hF : Finite s F)
    (hE : ∀k∈E,2*k ≤ n ∧ (k:ℝ)/(n:ℝ) ≤ Real.log sigma) :
    (∑k∈E,|factorialRecoveryRatio n k-∑a∈Finset.range (p+1),H k a/(n:ℝ)^a| *‖F.coeff k‖*r^k) ≤
      (WeightedPolynomialMultiplier.moment (sigma*r/s) (2*(p+1))/(n:ℝ)^(p+1))*norm s F := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hsigma0 : 0 ≤ sigma := by linarith
  calc
    _ ≤ ∑k∈E,(1/(n:ℝ)^(p+1))*((k:ℝ)^(2*(p+1))*sigma^k*‖F.coeff k‖*r^k) := by
      apply Finset.sum_le_sum
      intro k hk
      have hwin := hE k hk
      have he := RecoveryFiniteOrderRemainder.remainder n k p hn (by omega)
      rw [abs_of_nonneg he.1]
      have hp := factorialRecoveryRatio_le_pow n k hn hwin.1 sigma hsigma hwin.2
      have hb := he.2.trans (mul_le_mul_of_nonneg_right hp (by positivity))
      have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb (norm_nonneg (F.coeff k))) (pow_nonneg hr k)
      convert hm using 1 <;> simp only [div_pow,pow_mul] <;> ring
    _ = (1/(n:ℝ)^(p+1))*(∑k∈E,(k:ℝ)^(2*(p+1))*sigma^k*‖F.coeff k‖*r^k) := by rw [Finset.mul_sum]
    _ ≤ (1/(n:ℝ)^(p+1))*(WeightedPolynomialMultiplier.moment (sigma*r/s) (2*(p+1))*norm s F) :=
      mul_le_mul_of_nonneg_left (WeightedPolynomialMultiplier.finite_window F E _ r s sigma hr hs hsigma0 hgap hF) (by positivity)
    _ = _ := by ring
end FactorialWeightedRemainder
#print axioms FactorialWeightedRemainder.bound
