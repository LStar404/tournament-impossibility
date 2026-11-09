import RecoveryHomogeneousEvaluation
noncomputable section
namespace RecoveryFiniteOrderRemainder
open RecoveryHomogeneousList RecoveryHomogeneousEvaluation FiniteFactorialRecovery

def nodes : ℕ → List ℝ
  | 0 => []
  | k+1 => nodes k++[(k:ℝ)]

theorem nodes_range (k : ℕ) : nodes k=(List.range k).map (fun i : ℕ => (i:ℝ)) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [nodes,ih,List.range_succ]

theorem nodes_mem (k : ℕ) (x : ℝ) (hx : x∈nodes k) : 0 ≤ x ∧ x<(k:ℝ) := by
  rw [nodes_range] at hx
  have hx' : ∃i:ℕ,i∈List.range k ∧ (i:ℝ)=x := List.mem_map.mp hx
  obtain ⟨i,hi,rfl⟩ := hx'
  exact ⟨Nat.cast_nonneg i,by exact_mod_cast List.mem_range.mp hi⟩

theorem nodes_sum_bound (k : ℕ) : (nodes k).sum ≤ (k:ℝ)^2 := by
  induction k with
  | zero => simp [nodes]
  | succ k ih => simp only [nodes,List.sum_append,List.sum_singleton,Nat.cast_add,Nat.cast_one]; nlinarith

theorem product_ratio (n k : ℕ) (hn : 0<n) (hk : k ≤ n) :
    product (nodes k) (1/(n:ℝ))=factorialRecoveryRatio n k := by
  induction k with
  | zero => simp [nodes,product,factorialRecoveryRatio]
  | succ k ih =>
    have hkn : k<n := by omega
    have hnR : (0:ℝ)<n := by exact_mod_cast hn
    rw [nodes,product,List.map_append,List.prod_append,List.map_singleton,List.prod_singleton]
    change product (nodes k) (1/(n:ℝ))*(1-(k:ℝ)*(1/(n:ℝ)))⁻¹=factorialRecoveryRatio n (k+1)
    rw [ih (by omega),factorialRecoveryRatio_succ n k hn hkn]
    have hi : (1-(k:ℝ)*(1/(n:ℝ)))⁻¹=(n:ℝ)/((n:ℝ)-(k:ℝ)) := by field_simp
    rw [hi,mul_comm]

def H (k a : ℕ) : ℝ := coeff (nodes k) a

/-- Exact factorial-ratio remainder, not an assumed proxy. Includes k=0,1 and all p≥0. -/
theorem remainder (n k p : ℕ) (hn : 0<n) (hk : k ≤ n) :
    0 ≤ factorialRecoveryRatio n k-∑a∈Finset.range (p+1),H k a/(n:ℝ)^a ∧
    factorialRecoveryRatio n k-∑a∈Finset.range (p+1),H k a/(n:ℝ)^a ≤
      factorialRecoveryRatio n k*((k:ℝ)^2/(n:ℝ))^(p+1) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hL : ∀x∈nodes k,0 ≤ x ∧ x*(1/(n:ℝ))<1 := by
    intro x hx
    have hh := nodes_mem k x hx
    constructor
    · exact hh.1
    · rw [mul_one_div]
      apply (div_lt_one hnR).mpr
      exact hh.2.trans_le (by exact_mod_cast hk)
  have hh := RecoveryHomogeneousEvaluation.remainder (nodes k) (1/(n:ℝ)) (by positivity) hL p
  rw [product_ratio n k hn hk] at hh
  simp only [one_div_pow,mul_one_div] at hh
  change 0 ≤ factorialRecoveryRatio n k-∑a∈Finset.range (p+1),H k a/(n:ℝ)^a ∧ _ at hh
  refine ⟨hh.1,hh.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (le_of_lt (factorialRecoveryRatio_pos n k hn hk))
  have hsum0 : 0 ≤ (nodes k).sum := List.sum_nonneg (fun x hx => (nodes_mem k x hx).1)
  apply pow_le_pow_left₀ (by positivity)
  exact div_le_div_of_nonneg_right (nodes_sum_bound k) hnR.le
end RecoveryFiniteOrderRemainder
#print axioms RecoveryFiniteOrderRemainder.remainder
