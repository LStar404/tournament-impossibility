import VectorWeakMajorization
namespace MajorizationCone
open Finset VectorWeakMajorization

/-- Zero-based penalty weights 1,1,3,3,... -/
def penalty (j : ℕ) : ℕ := 1 + 2 * (j / 2)
lemma penalty_mono : Monotone penalty := by
  intro a b hab
  simp only [penalty]
  omega
lemma penalty_le (j : ℕ) : penalty j ≤ j + 1 := by
  unfold penalty
  omega

def pWeight (n k i : ℕ) : ℝ :=
  if i < n then if i < n-k then (k : ℝ) else (k : ℝ) - penalty (i-(n-k)) else 0

def P (n k : ℕ) (x : ℕ → ℝ) : ℝ := ∑ i ∈ range n, pWeight n k i * x i

theorem pWeight_nonnegative (n k i : ℕ) (hk : k ≤ n) : 0 ≤ pWeight n k i := by
  unfold pWeight
  split_ifs with hi hleft
  · positivity
  · have hp := penalty_le (i-(n-k))
    have hh : penalty (i-(n-k)) ≤ k := by omega
    exact sub_nonneg.mpr (by exact_mod_cast hh)
  · rfl

theorem pWeight_descending (n k i : ℕ) (hk : k ≤ n) :
    pWeight n k (i+1) ≤ pWeight n k i := by
  by_cases hn : i+1 < n
  · have hi : i < n := by omega
    simp only [pWeight, if_pos hn, if_pos hi]
    split_ifs with ha hb hb
    · rfl
    · omega
    · have hh : (0 : ℝ) ≤ penalty (i+1-(n-k)) := by positivity
      linarith
    · have hp := penalty_mono (show i-(n-k) ≤ i+1-(n-k) by omega)
      have hp' : (penalty (i-(n-k)) : ℝ) ≤ penalty (i+1-(n-k)) := by exact_mod_cast hp
      linarith
  · simp only [pWeight, if_neg hn]
    exact pWeight_nonnegative n k i hk

theorem P_preserves_prefix_order (n k : ℕ) (hk : k ≤ n) (x y : ℕ → ℝ)
    (h : WeakMajorized n x y) : P n k x ≤ P n k y := by
  apply weighted_le n x y (pWeight n k) h
  exact ⟨fun i _ => pWeight_nonnegative n k i hk,
    fun i _ => pWeight_descending n k i hk⟩

/-- Penalty increment c_h, with c_0=0. -/
def increment (h : ℕ) : ℕ := if h = 0 then 0 else penalty (h-1)
lemma increment_le (h : ℕ) : increment h ≤ h := by
  unfold increment
  split_ifs with hh
  · omega
  · have := penalty_le (h-1); omega
lemma increment_mono : Monotone increment := by
  intro a b hab
  unfold increment
  split_ifs with ha hb hb
  · rfl
  · omega
  · omega
  · exact penalty_mono (by omega)

/-- The output coordinate on the prefix generator of length l. -/
def generatorImage (n l k : ℕ) : ℝ :=
  (l : ℝ) - increment ((k+1)-(n-l))

theorem generatorImage_nonnegative (n l k : ℕ) (hl : l ≤ n) (hk : k < n) :
    0 ≤ generatorImage n l k := by
  have h := increment_le ((k+1)-(n-l))
  have hh : increment ((k+1)-(n-l)) ≤ l := by omega
  unfold generatorImage
  exact sub_nonneg.mpr (by exact_mod_cast hh)

theorem generatorImage_descending (n l k : ℕ) :
    generatorImage n l (k+1) ≤ generatorImage n l k := by
  have h := increment_mono (show (k+1)-(n-l) ≤ (k+1+1)-(n-l) by omega)
  unfold generatorImage
  have hh : (increment ((k+1)-(n-l)) : ℝ) ≤ increment ((k+1+1)-(n-l)) := by exact_mod_cast h
  linarith

lemma entry_identity (n k i : ℕ) (hk : k < n) (hi : i < n) :
    pWeight n (k+1) i - pWeight n k i =
      generatorImage n (i+1) k - generatorImage n i k := by
  have hh :
      (if i < n-(k+1) then ((k+1 : ℕ) : ℤ) else ((k+1 : ℕ) : ℤ) - (penalty (i-(n-(k+1))) : ℤ)) -
      (if i < n-k then (k : ℤ) else (k : ℤ) - (penalty (i-(n-k)) : ℤ)) =
      (((i+1 : ℕ) : ℤ) - (increment ((k+1)-(n-(i+1))) : ℤ)) -
      ((i : ℤ) - (increment ((k+1)-(n-i)) : ℤ)) := by
    unfold increment penalty
    split_ifs <;> push_cast <;> omega
  unfold pWeight generatorImage
  simp only [if_pos hi]
  exact_mod_cast hh

/-- Cone-generator implementation; identification with P differences is a
separate interface, not assumed as a hypothesis of the cone theorem. -/
def coneOperator (n : ℕ) (x : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k < n then ∑ l ∈ range n, (x l - x (l+1)) * generatorImage n (l+1) k else 0

theorem coneOperator_preserves_cone (n : ℕ) (x : ℕ → ℝ)
    (hx : DescendingNonnegative n x) : DescendingNonnegative n (coneOperator n x) := by
  constructor
  · intro k hk
    unfold coneOperator
    split_ifs with hkn
    · apply sum_nonneg
      intro l hl
      exact mul_nonneg (sub_nonneg.mpr (hx.2 l (mem_range.mp hl)))
        (generatorImage_nonnegative n (l+1) k (by simpa using mem_range.mp hl) hkn)
    · rfl
  · intro k hk
    by_cases hkn : k+1 < n
    · simp only [coneOperator, if_pos hkn, if_pos hk]
      apply sum_le_sum
      intro l hl
      exact mul_le_mul_of_nonneg_left (generatorImage_descending n (l+1) k)
        (sub_nonneg.mpr (hx.2 l (mem_range.mp hl)))
    · simp only [coneOperator, if_neg hkn, if_pos hk]
      apply sum_nonneg
      intro l hl
      exact mul_nonneg (sub_nonneg.mpr (hx.2 l (mem_range.mp hl)))
        (generatorImage_nonnegative n (l+1) k (by simpa using mem_range.mp hl) hk)

lemma difference_prefix (n k l : ℕ) (hk : k < n) (hl : l ≤ n) :
    prefixSum (fun i => pWeight n (k+1) i - pWeight n k i) l =
      generatorImage n l k := by
  induction l with
  | zero =>
    have hh : k+1-n = 0 := by omega
    simp [prefixSum, generatorImage, increment, hh]
  | succ l ih =>
    have ih' := ih (by omega)
    simp only [prefixSum, sum_range_succ] at *
    rw [ih', entry_identity n k l hk (by omega)]
    ring

def K (n : ℕ) (x : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k < n then P n (k+1) x - P n k x else 0

/-- The P-difference operator equals the proved cone-generator operator.
The endpoint x(n)=0 is the usual zero padding of a finite vector. -/
theorem K_eq_coneOperator (n : ℕ) (x : ℕ → ℝ) (hx : x n = 0) :
    K n x = coneOperator n x := by
  funext k
  by_cases hk : k < n
  · simp only [K, coneOperator, if_pos hk, P]
    rw [← sum_sub_distrib]
    have he : (∑ i ∈ range n, (pWeight n (k+1) i * x i - pWeight n k i * x i)) =
        ∑ i ∈ range n, x i * (pWeight n (k+1) i - pWeight n k i) := by
      apply sum_congr rfl; intro i hi; ring
    rw [he, abel n x (fun i => pWeight n (k+1) i - pWeight n k i), hx]
    simp only [zero_mul, zero_add]
    apply sum_congr rfl; intro l hl
    rw [difference_prefix n k (l+1) hk (by simpa using mem_range.mp hl)]
  · simp [K, coneOperator, hk]

theorem K_preserves_cone (n : ℕ) (x : ℕ → ℝ)
    (hx : DescendingNonnegative n x) (hzero : x n = 0) :
    DescendingNonnegative n (K n x) := by
  rw [K_eq_coneOperator n x hzero]
  exact coneOperator_preserves_cone n x hx


lemma P_zero (n : ℕ) (x : ℕ → ℝ) : P n 0 x = 0 := by
  unfold P
  apply sum_eq_zero
  intro i hi
  simp [pWeight, mem_range.mp hi]

lemma prefix_K (n l : ℕ) (hl : l ≤ n) (x : ℕ → ℝ) :
    prefixSum (K n x) l = P n l x := by
  induction l with
  | zero => simp [prefixSum, P_zero]
  | succ l ih =>
    have hh : l < n := by omega
    have hi := ih (by omega)
    simp only [prefixSum, sum_range_succ] at *
    rw [hi]
    simp only [K, if_pos hh]
    ring

theorem K_preserves_prefix_order (n : ℕ) (x y : ℕ → ℝ)
    (h : WeakMajorized n x y) : WeakMajorized n (K n x) (K n y) := by
  intro k hk
  rw [prefix_K n k hk x, prefix_K n k hk y]
  exact P_preserves_prefix_order n k hk x y h


/-- Identification of the coefficient definition with the selected-tail formula. -/
theorem P_tail_formula (n k : ℕ) (hk : k ≤ n) (x : ℕ → ℝ) :
    P n k x = (k : ℝ) * (∑ i ∈ range n, x i) -
      ∑ j ∈ range k, (penalty j : ℝ) * x (n-k+j) := by
  let q : ℕ → ℝ := fun i => if i < n-k then 0 else (penalty (i-(n-k)) : ℝ) * x i
  have hsplit : (∑ i ∈ range n, q i) =
      (∑ i ∈ range (n-k), q i) + ∑ j ∈ range k, q (n-k+j) := by
    have hh := sum_range_add q (n-k) k
    have he : n-k+k = n := by omega
    rw [he] at hh
    exact hh
  have hzero : (∑ i ∈ range (n-k), q i) = 0 := by
    apply sum_eq_zero
    intro i hi
    simp [q, mem_range.mp hi]
  have htail : (∑ j ∈ range k, q (n-k+j)) =
      ∑ j ∈ range k, (penalty j : ℝ) * x (n-k+j) := by
    apply sum_congr rfl
    intro j hj
    have hh : ¬ n-k+j < n-k := by omega
    simp [q, hh]
  rw [hzero, htail, zero_add] at hsplit
  unfold P
  have he : (∑ i ∈ range n, pWeight n k i * x i) =
      ∑ i ∈ range n, ((k : ℝ) * x i - q i) := by
    apply sum_congr rfl
    intro i hi
    simp only [pWeight, if_pos (mem_range.mp hi), q]
    split_ifs <;> ring
  rw [he, sum_sub_distrib, ← mul_sum, hsplit]

end MajorizationCone
#print axioms MajorizationCone.P_preserves_prefix_order
#print axioms MajorizationCone.coneOperator_preserves_cone

#print axioms MajorizationCone.K_preserves_cone

#print axioms MajorizationCone.K_preserves_prefix_order

#print axioms MajorizationCone.P_tail_formula
