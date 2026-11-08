import BalancedSignCounts
namespace SelectedSignPairs
open Finset
open BalancedSignCounts

def sign (s : Bool) : ℝ := if s then 1 else -1

def pairCost (s : ℕ → Bool) (b : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ range n, ∑ i ∈ range j, |sign (s i)*b j-sign (s j)*b i|

lemma edge_formula (si sj : Bool) (a b : ℝ) (hb : 0≤b) (hba : b≤a) :
    |sign si*b-sign sj*a| = a+b-2*b*(if si=sj then 1 else 0) := by
  cases si <;> cases sj <;> simp [sign]
  · rw [abs_of_nonneg (by linarith)]
    ring
  · rw [abs_of_nonpos (by linarith)]
    ring
  · rw [abs_of_nonneg (by linarith)]
    ring
  · rw [abs_of_nonpos (by linarith)]
    ring

lemma row_formula (s : ℕ → Bool) (b : ℕ → ℝ) (j : ℕ)
    (hb : 0 ≤ b j) (hd : ∀ i<j, b j ≤ b i) :
    (∑ i ∈ range j, |sign (s i)*b j-sign (s j)*b i|) =
      (∑ i ∈ range j, b i) + (j : ℝ)*b j-2*b j*prior s j := by
  have he : (∑ i ∈ range j, |sign (s i)*b j-sign (s j)*b i|) =
      ∑ i ∈ range j, (b i+b j-2*b j*(if s i=s j then 1 else 0)) := by
    apply sum_congr rfl; intro i hi
    exact edge_formula (s i) (s j) (b i) (b j) hb (hd i (mem_range.mp hi))
  rw [he]
  simp only [sum_sub_distrib, sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul]
  have hc : (∑ i ∈ range j, (if s i=s j then (1:ℝ) else 0)) = prior s j := by
    simp [prior, count]
  rw [hc]

/-- Exact internal pair cost for arbitrary selected signs and decreasing weights. -/
theorem pairCost_identity (s : ℕ → Bool) (b : ℕ → ℝ) (n : ℕ)
    (hb : ∀ j<n, 0 ≤ b j) (hd : ∀ i j, i<j → j<n → b j ≤ b i) :
    pairCost s b n = (n : ℝ)*(∑ j ∈ range n, b j) -
      (∑ j ∈ range n, b j) - 2*(∑ j ∈ range n, b j*prior s j) := by
  induction n with
  | zero => simp [pairCost]
  | succ n ih =>
    have hi := ih (fun j hj => hb j (by omega))
      (fun i j hij hj => hd i j hij (by omega))
    have hr := row_formula s b n (hb n (by omega))
      (fun i hi => hd i n hi (by omega))
    have hp : pairCost s b (n+1) = pairCost s b n +
        ∑ i ∈ range n, |sign (s i)*b n-sign (s n)*b i| := by
      simp [pairCost, sum_range_succ]
    rw [hp, hi, hr, sum_range_succ, sum_range_succ]
    push_cast
    ring

/-- Optimizing signs yields the alternating-sign penalty, without assuming the
chosen signs themselves alternate. -/
theorem pairCost_le (s : ℕ → Bool) (b : ℕ → ℝ) (n : ℕ)
    (hb : VectorWeakMajorization.DescendingNonnegative n b)
    (hd : ∀ i j, i<j → j<n → b j ≤ b i) :
    pairCost s b n ≤ (n : ℝ)*(∑ j ∈ range n, b j) -
      ∑ j ∈ range n, (1+2*(j/2 : ℕ))*b j := by
  have hi := pairCost_identity s b n (fun j hj => hb.1 j (by omega)) hd
  have hp := penalty_le s n b hb
  have he : (∑ j ∈ range n, (1+2*prior s j)*b j) =
      (∑ j ∈ range n, b j)+2*(∑ j ∈ range n, b j*prior s j) := by
    rw [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl; intro j hj; ring
  rw [he] at hp
  linarith

end SelectedSignPairs
#print axioms SelectedSignPairs.pairCost_identity
#print axioms SelectedSignPairs.pairCost_le
