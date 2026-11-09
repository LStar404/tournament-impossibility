import ActualCoreWeightedBound
import PermanentCoreFiniteRecovery
import FactorialLinearWindow
import ActivityFiniteWindowBound

/-! Actual fixed-depth core-activity bounds and finite activity windows.
The core hypothesis of the earlier recovery theorem is discharged here. -/
noncomputable section
namespace ActualGraphCoreRecovery
open WeightedCoefficientNorm ActualResidualFrozenFactorization BinaryGraphActivityBound
open FiniteFactorialRecovery

def activityConstant (d : ℕ) : ℝ := QuantitativeFixedActivity.totalConstant (coordinateConstant d)
def cutoff (d : ℕ) : ℝ := min FactorialLinearWindow.alpha (1/(4*Real.exp 1*activityConstant d))
def degree (d n : ℕ) : ℕ := ⌊cutoff d*(n : ℝ)⌋₊
def window (d n : ℕ) : Finset ℕ := Finset.range (degree d n+1)
def lowConstant (d p : ℕ) : ℝ := ∑ j ∈ Finset.range (p+1),
  WeightedPolynomialMultiplier.moment (17/18) (2*(p-j+1))*
    (ActualCoreWeightedBound.coreConstant d*(activityConstant d*(j : ℝ))^j)
def highConstant (d p : ℕ) : ℝ :=
  ActualCoreWeightedBound.coreConstant d*(2*(activityConstant d*((p : ℝ)+1))^(p+1))

lemma activityConstant_pos (d : ℕ) : 0<activityConstant d := by
  unfold activityConstant QuantitativeFixedActivity.totalConstant coordinateConstant
  positivity
lemma cutoff_pos (d : ℕ) : 0<cutoff d :=
  lt_min FactorialLinearWindow.alpha_positive (by unfold activityConstant QuantitativeFixedActivity.totalConstant coordinateConstant; positivity)
lemma coreConstant_nonneg (d : ℕ) : 0≤ActualCoreWeightedBound.coreConstant d := (Real.exp_pos _).le

lemma budget (d n k : ℕ) (hn : 0<n) (hk : k∈window d n) :
    2*k≤n ∧ (k : ℝ)/(n : ℝ)≤Real.log (17/16) := by
  apply FactorialLinearWindow.budget n k hn
  have hfloor : degree d n≤⌊FactorialLinearWindow.alpha*(n : ℝ)⌋₊ :=
    Nat.floor_mono (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg n))
  simp only [window, Finset.mem_range] at hk
  simp only [FactorialLinearWindow.window, Finset.mem_range]
  omega

lemma recovered_window (n : ℕ) (hn : 0<n) (F : PowerSeries ℂ)
    (E : Finset ℕ) (hF : Finite (9/8) F)
    (hE : ∀ k∈E, 2*k≤n ∧ (k : ℝ)/(n : ℝ)≤Real.log (17/16)) :
    (∑ k∈E, factorialRecoveryRatio n k*‖F.coeff k‖)≤norm (9/8) F := by
  calc
    _ ≤ ∑ k∈E, mass (9/8) F k := by
      apply Finset.sum_le_sum
      intro k hk
      have hb := factorialRecoveryRatio_le_pow n k hn (hE k hk).1 (17/16) (by norm_num) (hE k hk).2
      have hp : (17/16 : ℝ)^k≤(9/8 : ℝ)^k := pow_le_pow_left₀ (by norm_num) (by norm_num) k
      simpa only [mass, mul_comm] using mul_le_mul_of_nonneg_right (hb.trans hp) (norm_nonneg (F.coeff k))
    _ ≤ _ := hF.sum_le_tsum E (fun k hk => nonneg (by norm_num) F k)

section Graph
variable {C : Type*} [Fintype C] [DecidableEq C] {n : ℕ}
variable (hn : 24≤n) (d : ℕ)
variable (e : BinaryBalancedTensor.Bits (d+1) ≃ Fin (2^(d+1))) (B : Matrix C C ℝ)
variable (hB : ∀ i j, B j i= -B i j) (he : ∀ i j, |B i j|≤1)
variable (f : Fin n ≃ C × BinaryBalancedTensor.Bits (d+1)) (v : ℝ) (hv : |v|≤1)
include hn hB he hv

/-- Direct instantiation of the old conditional positive-activity theorem. -/
theorem positive_order (p j : ℕ) (hj : 1≤j) (hjp : j≤p) :
    let M := TournamentSkewMargin.branch (BinaryRawGraphWeighted.realGraph (d+1) e B f) v
    ActivityFactorialMultiplier.error n (p-j) (core M*rawActivity M j) (window d n) 1 ≤
      (WeightedPolynomialMultiplier.moment (17/18) (2*(p-j+1))*
        (ActualCoreWeightedBound.coreConstant d*(activityConstant d*(j : ℝ))^j))/(n : ℝ)^(p+1) := by
  have h := PermanentCoreFiniteRecovery.graph_order_bound hn d e B hB he f v hv p j hj hjp
    (window d n) 1 (17/16) (ActualCoreWeightedBound.coreConstant d)
    (by norm_num) (by norm_num) (by norm_num) (fun k hk => budget d n k (by omega) hk)
    (ActualCoreWeightedBound.graph hn d e B hB he f v hv)
  simpa only [mul_one, show (17/16 : ℝ)/(9/8)=17/18 by norm_num, activityConstant] using h

theorem order (p j : ℕ) (hjp : j≤p) :
    let M := TournamentSkewMargin.branch (BinaryRawGraphWeighted.realGraph (d+1) e B f) v
    ActivityFactorialMultiplier.error n (p-j) (core M*rawActivity M j) (window d n) 1 ≤
      (WeightedPolynomialMultiplier.moment (17/18) (2*(p-j+1))*
        (ActualCoreWeightedBound.coreConstant d*(activityConstant d*(j : ℝ))^j))/(n : ℝ)^(p+1) := by
  by_cases hj : j=0
  · subst j
    dsimp only
    rw [CoreActivityFiniteProjection.zero_activity_product]
    have hG := ActualCoreWeightedBound.graph hn d e B hB he f v hv
    dsimp only at hG
    have h := CoreActivityFactorialBridge.zeroth_order_bound n p (by omega) _ (window d n)
      1 (9/8) (17/16) (ActualCoreWeightedBound.coreConstant d)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hG.1 hG.2
      (fun k hk => budget d n k (by omega) hk)
    simpa only [Nat.sub_zero, Nat.cast_zero, mul_zero, pow_zero, mul_one,
      show (17/16 : ℝ)/(9/8)=17/18 by norm_num] using h
  · exact positive_order hn d e B hB he f v hv p j (by omega) hjp

theorem low_sum (p : ℕ) :
    let M := TournamentSkewMargin.branch (BinaryRawGraphWeighted.realGraph (d+1) e B f) v
    (∑ j∈Finset.range (p+1), ActivityFactorialMultiplier.error n (p-j)
      (core M*rawActivity M j) (window d n) 1)≤lowConstant d p/(n : ℝ)^(p+1) := by
  dsimp only
  calc
    _ ≤ ∑ j∈Finset.range (p+1),
        (WeightedPolynomialMultiplier.moment (17/18) (2*(p-j+1))*
          (ActualCoreWeightedBound.coreConstant d*(activityConstant d*(j : ℝ))^j))/(n : ℝ)^(p+1) := by
      apply Finset.sum_le_sum
      intro j hj
      exact order hn d e B hB he f v hv p j (by simpa using hj)
    _ = _ := by rw [← Finset.sum_div]; rfl

theorem product_bound (j : ℕ) (hj : 1≤j) :
    let M := TournamentSkewMargin.branch (BinaryRawGraphWeighted.realGraph (d+1) e B f) v
    Finite (9/8) (core M*rawActivity M j) ∧ norm (9/8) (core M*rawActivity M j)≤
      ActualCoreWeightedBound.coreConstant d*(activityConstant d*(j : ℝ)/(n : ℝ))^j := by
  have hG := ActualCoreWeightedBound.graph hn d e B hB he f v hv
  have hC := BinaryGraphActivityBound.bound hn d e B hB he f v hv j hj
  dsimp only at hG hC ⊢
  refine ⟨finite_mul (by norm_num) hG.1 hC.1, ?_⟩
  exact (mul_bound (by norm_num) hG.1 hC.1).trans
    (mul_le_mul hG.2 hC.2 (norm_nonnegative (by norm_num) _) (coreConstant_nonneg d))

theorem high_sum (p : ℕ) :
    let M := TournamentSkewMargin.branch (BinaryRawGraphWeighted.realGraph (d+1) e B f) v
    (∑ j∈Finset.Ico (p+1) (degree d n+1), ∑ k∈window d n,
      factorialRecoveryRatio n k*‖(core M*rawActivity M j).coeff k‖)≤
        highConstant d p/(n : ℝ)^(p+1) := by
  dsimp only
  have hh := ActivityFiniteWindowBound.dominated_floor_window (activityConstant_pos d)
    (cutoff_pos d).le (min_le_right _ _) (coreConstant_nonneg d) n p (by omega)
    (fun j => ∑ k∈window d n, factorialRecoveryRatio n k*‖(core
      (TournamentSkewMargin.branch (BinaryRawGraphWeighted.realGraph (d+1) e B f) v)*
      rawActivity (TournamentSkewMargin.branch (BinaryRawGraphWeighted.realGraph (d+1) e B f) v) j).coeff k‖) ?_
  · simpa only [degree, highConstant, mul_div_assoc] using hh
  · intro j hj
    have hj1 : 1≤j := by simp only [Finset.mem_Ico] at hj; omega
    have hb := product_bound hn d e B hB he f v hv j hj1
    dsimp only at hb
    exact (recovered_window n (by omega) _ (window d n) hb.1
      (fun k hk => budget d n k (by omega) hk)).trans hb.2
end Graph
end ActualGraphCoreRecovery
#print axioms ActualGraphCoreRecovery.positive_order
#print axioms ActualGraphCoreRecovery.low_sum
#print axioms ActualGraphCoreRecovery.high_sum
