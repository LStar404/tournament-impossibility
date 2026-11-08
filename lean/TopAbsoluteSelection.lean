import TournamentSwitching
noncomputable section
namespace TopAbsoluteSelection
open Finset VectorWeakMajorization TournamentSwitching

def embedding {n : ℕ} (x : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) : Fin k ↪ Fin n :=
  (Fin.castLEEmb hk).trans (absSort x).toEmbedding

def topSet {n : ℕ} (x : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) : Finset (Fin n) :=
  univ.map (embedding x k hk)

theorem card_topSet {n : ℕ} (x : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    (topSet x k hk).card = k := by simp [topSet]

theorem sum_topSet {n : ℕ} (x : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    (∑ i ∈ topSet x k hk, |x i|) = prefixSum (sortedPad x) k := by
  simp only [topSet, sum_map]
  rw [prefixSum, ← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro j hj
  have hjn : j.val < n := lt_of_lt_of_le j.isLt hk
  simp [embedding, sortedPad, hjn, Fin.castLE]

/-- The largest-k absolute sum is an actual signed row selection. -/
theorem signed_topSet {n : ℕ} (x : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    (∑ i ∈ topSet x k hk, sign (x i) * x i) = prefixSum (sortedPad x) k := by
  simp only [sign_mul]
  exact sum_topSet x k hk
end TopAbsoluteSelection
#print axioms TopAbsoluteSelection.signed_topSet
