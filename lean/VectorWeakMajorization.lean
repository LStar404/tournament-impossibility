import Mathlib

/-! Finite weak-majorization core. This does not establish the tournament
selected-row estimate or the reference K orbit, and does not prove Assumption R. -/
namespace VectorWeakMajorization
open Finset

def prefixSum (x : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ range n, x i

def WeakMajorized (n : ℕ) (x y : ℕ → ℝ) : Prop :=
  ∀ k ≤ n, prefixSum x k ≤ prefixSum y k

def DescendingNonnegative (n : ℕ) (x : ℕ → ℝ) : Prop :=
  (∀ i ≤ n, 0 ≤ x i) ∧ (∀ i < n, x (i+1) ≤ x i)

/-- Endpoint-inclusive Abel formula; the value of w at n cancels. -/
theorem abel (n : ℕ) (w z : ℕ → ℝ) :
    (∑ i ∈ range n, w i * z i) =
      w n * prefixSum z n +
      ∑ i ∈ range n, (w i - w (i+1)) * prefixSum z (i+1) := by
  induction n with
  | zero => simp [prefixSum]
  | succ n ih =>
    rw [sum_range_succ, sum_range_succ, ih]
    have hp : prefixSum z (n+1) = prefixSum z n + z n := by
      simp [prefixSum, sum_range_succ]
    rw [hp]
    ring

/-- Decreasing nonnegative weights preserve all-prefixSum inequalities. -/
theorem weighted_le (n : ℕ) (x y w : ℕ → ℝ)
    (h : WeakMajorized n x y) (hw : DescendingNonnegative n w) :
    (∑ i ∈ range n, w i * x i) ≤ ∑ i ∈ range n, w i * y i := by
  rw [abel n w x, abel n w y]
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (h n le_rfl) (hw.1 n le_rfl)
  · apply sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left (h (i+1) (by simpa using mem_range.mp hi))
      (sub_nonneg.mpr (hw.2 i (mem_range.mp hi)))

/-- Squared Euclidean norm comparison, without importing a convexity theorem.
Use the descending nonnegative weight x+y; cross terms cancel. -/
theorem sum_sq_le (n : ℕ) (x y : ℕ → ℝ)
    (h : WeakMajorized n x y)
    (hx : DescendingNonnegative n x) (hy : DescendingNonnegative n y) :
    (∑ i ∈ range n, (x i)^2) ≤ ∑ i ∈ range n, (y i)^2 := by
  have hw : DescendingNonnegative n (fun i => x i + y i) := by
    constructor
    · intro i hi; exact add_nonneg (hx.1 i hi) (hy.1 i hi)
    · intro i hi; exact add_le_add (hx.2 i hi) (hy.2 i hi)
  have hh := weighted_le n x y (fun i => x i + y i) h hw
  have ha : (∑ i ∈ range n, (x i + y i) * x i) =
      (∑ i ∈ range n, (x i)^2) + ∑ i ∈ range n, x i * y i := by
    rw [← sum_add_distrib]; apply sum_congr rfl; intro i hi; ring
  have hb : (∑ i ∈ range n, (x i + y i) * y i) =
      (∑ i ∈ range n, (y i)^2) + ∑ i ∈ range n, x i * y i := by
    rw [← sum_add_distrib]; apply sum_congr rfl; intro i hi; ring
  rw [ha, hb] at hh
  linarith

/-- Actual real tournament sign matrices, not an abstract extremal sequence. -/
structure Tournament (n : ℕ) where
  entry : Fin n → Fin n → ℝ
  skew : ∀ i j, entry i j = -entry j i
  unit : ∀ i j, i ≠ j → entry i j = 1 ∨ entry i j = -1

namespace Tournament
variable {n : ℕ} (B : Tournament n)
theorem diagonal (i : Fin n) : B.entry i i = 0 := by
  have := B.skew i i
  linarith

def act (x : Fin n → ℝ) (i : Fin n) : ℝ := ∑ j, B.entry i j * x j
/-- The single-edge estimate used before optimizing selected rows. -/
theorem edge_bound (x y : Fin n → ℝ) (i j : Fin n) :
    B.entry i j * (y i * x j - y j * x i) ≤
      |y i * x j - y j * x i| := by
  by_cases hij : i = j
  · subst j; simp [B.diagonal]
  · rcases B.unit i j hij with h | h
    · rw [h, one_mul]; exact le_abs_self _
    · rw [h, neg_one_mul]; exact neg_le_abs _

/-- Skew-symmetry pairs the two oriented contributions exactly. -/
theorem pair_identity (x y : Fin n → ℝ) (i j : Fin n) :
    y i * B.entry i j * x j + y j * B.entry j i * x i =
      B.entry i j * (y i * x j - y j * x i) := by
  rw [B.skew j i]; ring

/-- Full finite signed-row pairing, before optimization over the row signs. -/
theorem signed_sum_identity (x y : Fin n → ℝ) :
    2 * (∑ i, y i * B.act x i) =
      ∑ i, ∑ j, B.entry i j * (y i * x j - y j * x i) := by
  have hswap : (∑ i, ∑ j, B.entry i j * (y j * x i)) =
      -(∑ i, ∑ j, B.entry i j * (y i * x j)) := by
    rw [sum_comm]
    rw [← sum_neg_distrib]
    apply sum_congr rfl; intro i hi
    rw [← sum_neg_distrib]
    apply sum_congr rfl; intro j hj
    rw [B.skew j i]; ring
  simp_rw [mul_sub, sum_sub_distrib]
  rw [hswap]
  have he : (∑ i, y i * B.act x i) =
      ∑ i, ∑ j, B.entry i j * (y i * x j) := by
    simp only [act, mul_sum]
    apply sum_congr rfl; intro i hi
    apply sum_congr rfl; intro j hj
    ring
  rw [he]; ring

/-- Universal signed selected-row upper bound. Choosing y in {-1,0,1}
recovers the starting point of the combinatorial optimization. -/
theorem signed_sum_bound (x y : Fin n → ℝ) :
    2 * (∑ i, y i * B.act x i) ≤
      ∑ i, ∑ j, |y i * x j - y j * x i| := by
  rw [B.signed_sum_identity]
  apply sum_le_sum; intro i hi
  apply sum_le_sum; intro j hj
  exact B.edge_bound x y i j

end Tournament
end VectorWeakMajorization

#print axioms VectorWeakMajorization.abel
#print axioms VectorWeakMajorization.weighted_le
#print axioms VectorWeakMajorization.sum_sq_le
#print axioms VectorWeakMajorization.Tournament.diagonal

#print axioms VectorWeakMajorization.Tournament.signed_sum_bound
