import PermanentNormalizedFrozenBridge
import CoreActivityFiniteProjection
import CoreActivityFactorialBridge

/-! Exact low-coefficient recovery and conditional core-activity multiplier
estimates. The arbitrary-depth uniform norm of the actual core remains a premise. -/
noncomputable section
namespace PermanentCoreFiniteRecovery
open PermanentNormalizedFrozenBridge ActualResidualFrozenFactorization
open BinaryGraphActivityBound WeightedCoefficientNorm

/-- Actual coefficients, not independently defined proxy coefficients. -/
theorem exact_coefficient {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hn : 0 < n)
    (m k : ℕ) (hk : k ≤ m) :
    (normalized M).coeff k =
      (FiniteFactorialRecovery.factorialRecoveryRatio n k : ℂ) *
        (∑ j ∈ Finset.range (m+1), core M * rawActivity M j).coeff k := by
  rw [coefficient_all M hn k, CoreActivityFiniteProjection.coefficient_projection M m k hk]

/-- Every positive activity in the actual graph has the required recovery order
after multiplication by the core. The core norm is deliberately explicit. -/
theorem graph_order_bound {C : Type*} [Fintype C] [DecidableEq C] {n : ℕ}
    (hn : 24 ≤ n) (depth : ℕ)
    (e : BinaryBalancedTensor.Bits (depth+1) ≃ Fin (2^(depth+1))) (B : Matrix C C ℝ)
    (hB : ∀ i j, B j i = -B i j) (he : ∀ i j, |B i j| ≤ 1)
    (f : Fin n ≃ C × BinaryBalancedTensor.Bits (depth+1)) (v : ℝ) (hv : |v| ≤ 1)
    (p j : ℕ) (hj : 1 ≤ j) (hjp : j ≤ p) (E : Finset ℕ)
    (r sigma L : ℝ) (hr : 0 ≤ r) (hsigma : 1 < sigma) (hgap : sigma*r < 9/8)
    (hE : ∀ k ∈ E, 2*k ≤ n ∧ (k : ℝ)/(n : ℝ) ≤ Real.log sigma)
    (hG : let M := TournamentSkewMargin.branch (BinaryRawGraphWeighted.realGraph (depth+1) e B f) v
      Finite (9/8) (core M) ∧ norm (9/8) (core M) ≤ L) :
    let M := TournamentSkewMargin.branch (BinaryRawGraphWeighted.realGraph (depth+1) e B f) v
    ActivityFactorialMultiplier.error n (p-j) (core M * rawActivity M j) E r ≤
      (WeightedPolynomialMultiplier.moment (sigma*r/(9/8)) (2*(p-j+1)) *
        (L*(QuantitativeFixedActivity.totalConstant (coordinateConstant depth)*(j : ℝ))^j)) /
          (n : ℝ)^(p+1) := by
  dsimp only at hG ⊢
  have hc := BinaryGraphActivityBound.bound hn depth e B hB he f v hv j hj
  dsimp only at hc
  apply CoreActivityFactorialBridge.product_order_bound n p j (by omega) hjp _ _ E
    r (9/8) sigma L _ hr (by norm_num) hsigma hgap _ hG.1 hc.1 hG.2
  · simpa only [div_pow] using hc.2
  · exact hE
  · unfold QuantitativeFixedActivity.totalConstant coordinateConstant
    positivity

end PermanentCoreFiniteRecovery

#print axioms PermanentCoreFiniteRecovery.exact_coefficient
#print axioms PermanentCoreFiniteRecovery.graph_order_bound
