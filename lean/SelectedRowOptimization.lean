import SelectedWeight
import SelectedSignPairs
namespace SelectedRowOptimization
open Finset MajorizationCone SelectedSignPairs VectorWeakMajorization

/-- Complete optimization of the selected/unselected edge-cost envelope.
This does not yet construct the envelope from the actual matrix row sum. -/
theorem envelope_le_P (n k : ℕ) (hk : k ≤ n) (f : ℕ → ℕ)
    (hf : ∀ i, i+1 < k → f i < f (i+1))
    (hr : ∀ i < k, f i < n) (x b : ℕ → ℝ) (s : ℕ → Bool)
    (hx : ∀ a c, a ≤ c → c < n → x c ≤ x a)
    (hb : DescendingNonnegative k b)
    (hd : ∀ i j, i<j → j<k → b j ≤ b i)
    (hselected : ∀ j<k, b j = x (f j)) :
    (k : ℝ) * ((∑ i ∈ range n, x i) - (∑ j ∈ range k, b j)) +
      pairCost s b k ≤ P n k x := by
  have hp := pairCost_le s b k hb hd
  have hw := SelectedWeight.selected_weight_ge n k hk f hf hr x hx
  have he : (∑ j ∈ range k, (penalty j : ℝ) * x (f j)) =
      ∑ j ∈ range k, (penalty j : ℝ) * b j := by
    apply sum_congr rfl
    intro j hj
    rw [hselected j (mem_range.mp hj)]
  rw [he] at hw
  have hpen : (∑ j ∈ range k, (penalty j : ℝ) * b j) =
      ∑ j ∈ range k, (1+2*(j/2 : ℕ))*b j := by
    apply sum_congr rfl
    intro j hj
    simp [penalty]
  rw [hpen] at hw
  rw [P_tail_formula n k hk x]
  nlinarith
end SelectedRowOptimization
#print axioms SelectedRowOptimization.envelope_le_P
