import MajorizationCone
namespace SelectedWeight
open Finset

/-- Finite strictly increasing enumeration has at least d index growth. -/
lemma growth (k : ℕ) (f : ℕ → ℕ)
    (hf : ∀ i, i+1 < k → f i < f (i+1))
    (j d : ℕ) (hd : j+d < k) : f j + d ≤ f (j+d) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hh := ih (by omega)
    have hs := hf (j+d) (by omega)
    have he : j+(d+1) = (j+d)+1 := by omega
    rw [he]
    omega

/-- The jth selected index lies no later than the jth index in the last k. -/
theorem selected_index_le (n k : ℕ) (f : ℕ → ℕ)
    (hf : ∀ i, i+1 < k → f i < f (i+1))
    (hr : ∀ i < k, f i < n) (j : ℕ) (hj : j < k) :
    f j ≤ n-k+j := by
  have h := growth k f hf j (k-1-j) (by omega)
  have he : j+(k-1-j) = k-1 := by omega
  rw [he] at h
  have hh := hr (k-1) (by omega)
  omega

/-- Selected decreasing coordinates dominate the smallest-k coordinates,
including their increasing positive penalty weights. -/
theorem selected_weight_ge (n k : ℕ) (hk : k ≤ n) (f : ℕ → ℕ)
    (hf : ∀ i, i+1 < k → f i < f (i+1))
    (hr : ∀ i < k, f i < n) (x : ℕ → ℝ)
    (hx : ∀ a b, a ≤ b → b < n → x b ≤ x a) :
    (∑ j ∈ range k, (MajorizationCone.penalty j : ℝ) * x (n-k+j)) ≤
      ∑ j ∈ range k, (MajorizationCone.penalty j : ℝ) * x (f j) := by
  apply sum_le_sum
  intro j hj
  have hj' := mem_range.mp hj
  apply mul_le_mul_of_nonneg_left
  · exact hx (f j) (n-k+j) (selected_index_le n k f hf hr j hj') (by omega)
  · positivity
end SelectedWeight
#print axioms SelectedWeight.selected_weight_ge
