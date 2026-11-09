import FactorialWeightedRemainder
import BinaryGraphActivityBound
import ActivityZeroNormalization
noncomputable section
namespace ActivityFactorialMultiplier
open FiniteFactorialRecovery RecoveryFiniteOrderRemainder WeightedCoefficientNorm

def error (n p : ℕ) (F : PowerSeries ℂ) (E : Finset ℕ) (r : ℝ) : ℝ :=
  ∑k∈E,|factorialRecoveryRatio n k-∑a∈Finset.range (p+1),H k a/(n:ℝ)^a| *‖F.coeff k‖*r^k

theorem order_bound (n p j : ℕ) (hn : 0<n) (hj : j ≤ p) (F : PowerSeries ℂ)
    (E : Finset ℕ) (r s sigma L : ℝ) (hr : 0 ≤ r) (hs : 0<s) (hsigma : 1<sigma)
    (hgap : sigma*r<s) (hF : Finite s F) (hb : norm s F ≤ L/(n:ℝ)^j)
    (hE : ∀k∈E,2*k ≤ n ∧ (k:ℝ)/(n:ℝ) ≤ Real.log sigma) :
    error n (p-j) F E r ≤
      (WeightedPolynomialMultiplier.moment (sigma*r/s) (2*(p-j+1))*L)/(n:ℝ)^(p+1) := by
  have hh := FactorialWeightedRemainder.bound n (p-j) hn F E r s sigma hr hs hsigma hgap hF hE
  have ht : 0 ≤ sigma*r/s := div_nonneg (mul_nonneg (by linarith) hr) hs.le
  have hm : 0 ≤ WeightedPolynomialMultiplier.moment (sigma*r/s) (2*(p-j+1)) :=
    tsum_nonneg (fun k => by positivity)
  apply hh.trans
  calc
    _ ≤ (WeightedPolynomialMultiplier.moment (sigma*r/s) (2*(p-j+1))/(n:ℝ)^(p-j+1))*(L/(n:ℝ)^j) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by rw [div_mul_div_comm,← pow_add,show p-j+1+j=p+1 by omega]

/-- Actual graph activity contribution to fixed-order factorial recovery. Core multiplication
and the permanent high-degree tail remain separate steps. -/
theorem graph_order_bound {C : Type*} [Fintype C] [DecidableEq C] {n : ℕ}
    (hn : 24 ≤ n) (depth : ℕ)
    (e : BinaryBalancedTensor.Bits (depth+1) ≃ Fin (2^(depth+1))) (B : Matrix C C ℝ)
    (hB : ∀i j,B j i= -B i j) (he : ∀i j,|B i j| ≤ 1)
    (f : Fin n ≃ C × BinaryBalancedTensor.Bits (depth+1)) (v : ℝ) (hv : |v| ≤ 1)
    (p j : ℕ) (hj : 1 ≤ j) (hjp : j ≤ p) (E : Finset ℕ)
    (r sigma : ℝ) (hr : 0 ≤ r) (hsigma : 1<sigma) (hgap : sigma*r<9/8)
    (hE : ∀k∈E,2*k ≤ n ∧ (k:ℝ)/(n:ℝ) ≤ Real.log sigma) :
    let M := TournamentSkewMargin.branch (BinaryRawGraphWeighted.realGraph (depth+1) e B f) v
    error n (p-j) (BinaryGraphActivityBound.rawActivity M j) E r ≤
      (WeightedPolynomialMultiplier.moment (sigma*r/(9/8)) (2*(p-j+1))*
        (QuantitativeFixedActivity.totalConstant (BinaryGraphActivityBound.coordinateConstant depth)*(j:ℝ))^j)/(n:ℝ)^(p+1) := by
  dsimp only
  have hb := BinaryGraphActivityBound.bound hn depth e B hB he f v hv j hj
  exact order_bound n p j (by omega) hjp _ E r (9/8) sigma _ hr (by norm_num)
    hsigma hgap hb.1 (by simpa only [div_pow] using hb.2) hE
theorem error_one (n p : ℕ) (E : Finset ℕ) (r : ℝ) :
    error n p (1:PowerSeries ℂ) E r=0 := by
  unfold error
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hk0 : k=0
  · subst k
    simp [factorialRecoveryRatio,H,RecoveryFiniteOrderRemainder.nodes,RecoveryHomogeneousList.coeff, ite_div]
  · simp [PowerSeries.coeff_one,hk0]

theorem zero_activity {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (p : ℕ) (E : Finset ℕ) (r : ℝ) :
    error n p (BinaryGraphActivityBound.rawActivity M 0) E r=0 := by
  have hzero : BinaryGraphActivityBound.rawActivity M 0=1 := ActivityZeroNormalization.zero _ _ _ _ _
  rw [hzero,error_one]
end ActivityFactorialMultiplier
#print axioms ActivityFactorialMultiplier.graph_order_bound
