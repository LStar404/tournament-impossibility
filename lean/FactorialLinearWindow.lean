import ActivityFactorialMultiplier
noncomputable section
namespace FactorialLinearWindow

def alpha : ℝ := Real.log (17/16)/2
def window (n : ℕ) : Finset ℕ := Finset.range (⌊alpha*(n:ℝ)⌋₊+1)

theorem alpha_positive : 0<alpha := by
  unfold alpha
  exact div_pos (Real.log_pos (by norm_num)) (by norm_num)

theorem budget (n k : ℕ) (hn : 0<n) (hk : k∈window n) :
    2*k ≤ n ∧ (k:ℝ)/(n:ℝ) ≤ Real.log (17/16) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have ha0 : 0 ≤ alpha := alpha_positive.le
  have hkN : k ≤ ⌊alpha*(n:ℝ)⌋₊ := by simpa [window] using hk
  have hkR : (k:ℝ) ≤ alpha*(n:ℝ) := (by exact_mod_cast hkN : (k:ℝ) ≤ (⌊alpha*(n:ℝ)⌋₊:ℝ)).trans
    (Nat.floor_le (by positivity))
  have ha : 2*alpha ≤ 1 := by
    have hl := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<17/16)
    unfold alpha
    norm_num at hl ⊢
    linarith
  have ha' : alpha ≤ Real.log (17/16) := by
    have hl := Real.log_pos (by norm_num : (1:ℝ)<17/16)
    unfold alpha
    linarith
  constructor
  · have hh := mul_le_mul_of_nonneg_right ha hnR.le
    have h : (2:ℝ)*(k:ℝ) ≤ n := by nlinarith
    exact_mod_cast h
  · exact ((div_le_iff₀ hnR).mpr hkR).trans ha'

/-- A concrete positive linear degree window for the actual graph activity recovery. -/
theorem graph {C : Type*} [Fintype C] [DecidableEq C] {n : ℕ}
    (hn : 24 ≤ n) (depth : ℕ)
    (e : BinaryBalancedTensor.Bits (depth+1) ≃ Fin (2^(depth+1))) (B : Matrix C C ℝ)
    (hB : ∀i j,B j i= -B i j) (he : ∀i j,|B i j| ≤ 1)
    (f : Fin n ≃ C × BinaryBalancedTensor.Bits (depth+1)) (v : ℝ) (hv : |v| ≤ 1)
    (p j : ℕ) (hj : 1 ≤ j) (hjp : j ≤ p) :
    let M := TournamentSkewMargin.branch (BinaryRawGraphWeighted.realGraph (depth+1) e B f) v
    ActivityFactorialMultiplier.error n (p-j) (BinaryGraphActivityBound.rawActivity M j) (window n) 1 ≤
      (WeightedPolynomialMultiplier.moment ((17/16)/(9/8)) (2*(p-j+1))*
        (QuantitativeFixedActivity.totalConstant (BinaryGraphActivityBound.coordinateConstant depth)*(j:ℝ))^j)/(n:ℝ)^(p+1) := by
  simpa only [mul_one] using ActivityFactorialMultiplier.graph_order_bound hn depth e B hB he f v hv p j hj hjp
    (window n) 1 (17/16) (by norm_num) (by norm_num) (by norm_num) (fun k hk => budget n k (by omega) hk)
end FactorialLinearWindow
#print axioms FactorialLinearWindow.graph
