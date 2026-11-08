import VectorWeakMajorization

namespace BalancedSignCounts
open Finset

def count (s : ℕ → Bool) (b : Bool) (n : ℕ) : ℕ :=
  ((range n).filter fun j => s j = b).card

def prior (s : ℕ → Bool) (j : ℕ) : ℝ := count s (s j) j

def pairs (s : ℕ → Bool) (n : ℕ) : ℝ := ∑ j ∈ range n, prior s j

lemma count_succ (s : ℕ → Bool) (b : Bool) (n : ℕ) :
    count s b (n+1) = count s b n + if s n = b then 1 else 0 := by
  by_cases h : s n = b <;> simp [count, range_add_one, filter_insert, h]

lemma count_partition (s : ℕ → Bool) (n : ℕ) :
    count s true n + count s false n = n := by
  induction n with
  | zero => simp [count]
  | succ n ih =>
    rw [count_succ, count_succ]
    cases s n <;> simp <;> omega

/-- Exact number of same-sign unordered pairs in a prefix, without division. -/
theorem pairs_identity (s : ℕ → Bool) (n : ℕ) :
    2 * pairs s n = (count s true n : ℝ)^2 + (count s false n : ℝ)^2 - n := by
  induction n with
  | zero => simp [pairs, count]
  | succ n ih =>
    have hd : pairs s (n+1) = pairs s n + prior s n := by
      simp [pairs, sum_range_succ]
    rw [hd, count_succ, count_succ]
    cases h : s n <;> simp [h, prior, Nat.cast_add] at * <;> nlinarith

/-- Balanced block sizes minimize the two squared counts. -/
theorem balanced_squares (p q n : ℕ) (hpq : p+q=n) :
    ((n/2 : ℕ) : ℝ)^2 + ((n-n/2 : ℕ) : ℝ)^2 ≤ (p : ℝ)^2+(q : ℝ)^2 := by
  have hm : n/2 ≤ n := Nat.div_le_self n 2
  have hr : n-n/2 ≤ n/2+1 := by omega
  have hh : p ≤ n/2 ∨ n-n/2 ≤ p := by omega
  have he : (p : ℝ)+(q : ℝ) = (n/2 : ℕ)+(n-n/2 : ℕ) := by exact_mod_cast (by omega : p+q=n/2+(n-n/2))
  have hm' : ((n/2 : ℕ) : ℝ) ≤ (n-n/2 : ℕ) := by exact_mod_cast (by omega : n/2 ≤ n-n/2)
  rcases hh with h | h
  · have hp : (p : ℝ) ≤ (n/2 : ℕ) := by exact_mod_cast h
    have hp' : (p : ℝ) ≤ (n-n/2 : ℕ) := le_trans hp hm'
    have hc := mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hp')
    nlinarith
  · have hp : ((n-n/2 : ℕ) : ℝ) ≤ p := by exact_mod_cast h
    have hp' : ((n/2 : ℕ) : ℝ) ≤ p := le_trans hm' hp
    have hc := mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hp')
    nlinarith

def baseline (n : ℕ) : ℝ := ∑ j ∈ range n, (j/2 : ℕ)

lemma baseline_identity (n : ℕ) :
    2 * baseline n = ((n/2 : ℕ) : ℝ)^2 + ((n-n/2 : ℕ) : ℝ)^2 - n := by
  induction n with
  | zero => simp [baseline]
  | succ n ih =>
    have hd : baseline (n+1) = baseline n + (n/2 : ℕ) := by
      simp [baseline, sum_range_succ]
    rw [hd]
    by_cases he : n % 2 = 0
    · have h1 : (n+1)/2=n/2 := by omega
      have h2 : n+1-(n+1)/2=(n-n/2)+1 := by omega
      have h3 : n-n/2=n/2 := by omega
      rw [h2, h1]
      push_cast
      rw [h3] at ih ⊢
      nlinarith
    · have h1 : (n+1)/2=n/2+1 := by omega
      have h2 : n+1-(n+1)/2=n-n/2 := by omega
      have h3 : n-n/2=n/2+1 := by omega
      rw [h2, h1]
      push_cast
      rw [h3] at ih ⊢
      push_cast at ih ⊢
      nlinarith

/-- Any sign prefix has at least the alternating-sign number of equal-sign pairs. -/
theorem baseline_le_pairs (s : ℕ → Bool) (n : ℕ) :
    baseline n ≤ pairs s n := by
  have hs := balanced_squares (count s true n) (count s false n) n (count_partition s n)
  have h1 := pairs_identity s n
  have h2 := baseline_identity n
  linarith

/-- Simultaneous prefix optimality transfers to every decreasing nonnegative weight. -/
theorem weighted_baseline_le (s : ℕ → Bool) (n : ℕ) (w : ℕ → ℝ)
    (hw : VectorWeakMajorization.DescendingNonnegative n w) :
    (∑ j ∈ range n, w j * (j/2 : ℕ)) ≤ ∑ j ∈ range n, w j * prior s j := by
  apply VectorWeakMajorization.weighted_le n (fun j => (j/2 : ℕ)) (prior s) w
  · intro k hk
    exact baseline_le_pairs s k
  · exact hw

/-- The exact c_j = 1+2 floor(j/2) penalty needed by the selected-row bound. -/
theorem penalty_le (s : ℕ → Bool) (n : ℕ) (w : ℕ → ℝ)
    (hw : VectorWeakMajorization.DescendingNonnegative n w) :
    (∑ j ∈ range n, (1 + 2 * (j/2 : ℕ)) * w j) ≤
      ∑ j ∈ range n, (1 + 2 * prior s j) * w j := by
  have h := weighted_baseline_le s n w hw
  have expand (f : ℕ → ℝ) :
      (∑ j ∈ range n, (1+2*f j)*w j) =
      (∑ j ∈ range n, w j) + 2*(∑ j ∈ range n, w j*f j) := by
    rw [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro j hj
    ring
  rw [expand, expand]
  linarith

end BalancedSignCounts

#print axioms BalancedSignCounts.baseline_le_pairs
#print axioms BalancedSignCounts.weighted_baseline_le

#print axioms BalancedSignCounts.penalty_le
