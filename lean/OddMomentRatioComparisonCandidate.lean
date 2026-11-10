import TournamentHamiltonian.Packing
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
Isolated candidate; see build/STATUS.json for compilation and audit evidence.
No sorry/admit/axiom. This is only the scalar finite-list analysis bridge.
It neither assumes nor establishes a tournament spectral-moment inequality.

Dependencies:
* TournamentHamiltonian.Packing: the existing `ratio` definition.
* Mathlib.Analysis.SpecialFunctions.Log.Deriv:
  `Real.hasSum_log_sub_log_of_abs_lt_one`.
* Standard HasSum.add, hasSum_zero, hasSum_le and real-log monotonicity.

List induction implements finite-sum HasSum transport, so duplicates are
retained and the two lists need not have the same length or be nonempty.
-/

namespace OddMomentRatioComparisonCandidate
open TournamentHamiltonian

lemma ratio_pos_of_mem_interval {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    0 < ratio x := by
  unfold ratio
  exact div_pos (by linarith) (by linarith)

lemma ratio_list_prod_pos (xs : List ℝ)
    (hx : ∀ x ∈ xs, 0 ≤ x ∧ x < 1) :
    0 < (xs.map ratio).prod := by
  revert hx
  induction xs with
  | nil => intro hx; simp
  | cons x xs ih =>
    intro hx
    have hhead := hx x (by simp)
    have htail : ∀ y ∈ xs, 0 ≤ y ∧ y < 1 := by
      intro y hy
      exact hx y (by simp [hy])
    simpa only [List.map_cons, List.prod_cons] using
      mul_pos (ratio_pos_of_mem_interval hhead.1 hhead.2) (ih htail)

/-- A singleton's log ratio has the standard nonnegative odd-power series. -/
theorem hasSum_log_ratio {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    HasSum (fun k : ℕ =>
      (2 : ℝ) * (1 / (2 * (k : ℝ) + 1)) * x ^ (2 * k + 1))
      (Real.log (ratio x)) := by
  have hx : |x| < 1 := by rwa [abs_of_nonneg h0]
  have hp : 1 + x ≠ 0 := ne_of_gt (by linarith : 0 < 1 + x)
  have hm : 1 - x ≠ 0 := ne_of_gt (by linarith : 0 < 1 - x)
  rw [ratio, Real.log_div hp hm]
  exact Real.hasSum_log_sub_log_of_abs_lt_one hx

/-- Finite-sum transport of the singleton series, retaining all multiplicities. -/
theorem hasSum_log_ratio_product (xs : List ℝ)
    (hx : ∀ x ∈ xs, 0 ≤ x ∧ x < 1) :
    HasSum (fun k : ℕ =>
      (2 : ℝ) * (1 / (2 * (k : ℝ) + 1)) *
        (xs.map (fun x => x ^ (2 * k + 1))).sum)
      (Real.log ((xs.map ratio).prod)) := by
  revert hx
  induction xs with
  | nil =>
    intro hx
    simpa only [List.map_nil, List.sum_nil, List.prod_nil, mul_zero,
      Real.log_one] using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0)
  | cons x xs ih =>
    intro hx
    have hhead := hx x (by simp)
    have htail : ∀ y ∈ xs, 0 ≤ y ∧ y < 1 := by
      intro y hy
      exact hx y (by simp [hy])
    have hp := ratio_pos_of_mem_interval hhead.1 hhead.2
    have hprod := ratio_list_prod_pos xs htail
    simpa only [List.map_cons, List.sum_cons, List.prod_cons, mul_add,
      Real.log_mul hp.ne' hprod.ne'] using
      (hasSum_log_ratio hhead.1 hhead.2).add (ih htail)

/-- Odd power moments alone suffice; full spectral majorization is not needed. -/
theorem ratio_product_le_of_odd_moments (xs ys : List ℝ)
    (hx : ∀ x ∈ xs, 0 ≤ x ∧ x < 1)
    (hy : ∀ y ∈ ys, 0 ≤ y ∧ y < 1)
    (hmom : ∀ k : ℕ,
      (xs.map (fun x => x ^ (2 * k + 1))).sum ≤
        (ys.map (fun y => y ^ (2 * k + 1))).sum) :
    (xs.map ratio).prod ≤ (ys.map ratio).prod := by
  have hlog : Real.log ((xs.map ratio).prod) ≤
      Real.log ((ys.map ratio).prod) := by
    apply hasSum_le _ (hasSum_log_ratio_product xs hx)
      (hasSum_log_ratio_product ys hy)
    intro k
    exact mul_le_mul_of_nonneg_left (hmom k) (by positivity)
  exact (Real.log_le_log_iff (ratio_list_prod_pos xs hx)
    (ratio_list_prod_pos ys hy)).mp hlog

/-- Convenient adapter when every positive integral moment is already known. -/
theorem ratio_product_le_of_positive_moments (xs ys : List ℝ)
    (hx : ∀ x ∈ xs, 0 ≤ x ∧ x < 1)
    (hy : ∀ y ∈ ys, 0 ≤ y ∧ y < 1)
    (hmom : ∀ r : ℕ, 0 < r →
      (xs.map (fun x => x ^ r)).sum ≤ (ys.map (fun y => y ^ r)).sum) :
    (xs.map ratio).prod ≤ (ys.map ratio).prod := by
  apply ratio_product_le_of_odd_moments xs ys hx hy
  intro k
  exact hmom (2 * k + 1) (by omega)

end OddMomentRatioComparisonCandidate

#print axioms OddMomentRatioComparisonCandidate.ratio_pos_of_mem_interval
#print axioms OddMomentRatioComparisonCandidate.ratio_list_prod_pos
#print axioms OddMomentRatioComparisonCandidate.hasSum_log_ratio
#print axioms OddMomentRatioComparisonCandidate.hasSum_log_ratio_product
#print axioms OddMomentRatioComparisonCandidate.ratio_product_le_of_odd_moments
#print axioms OddMomentRatioComparisonCandidate.ratio_product_le_of_positive_moments
