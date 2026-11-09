import PermanentCoreFiniteRecovery
import PermanentNormalizedTailBridge
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.Eval.Degree

/-! Finite truncated recovery polynomial and exact coefficient-error splitting.
This module neither forms nor assumes convergence of an infinite activity sum. -/
noncomputable section
namespace PermanentTruncatedRecoveryAlgebra
open ActualResidualFrozenFactorization BinaryGraphActivityBound
open PermanentNormalizedFrozenBridge FiniteFactorialRecovery

def multiplier (n q k : ℕ) : ℝ :=
  ∑ a∈Finset.range (q+1), RecoveryFiniteOrderRemainder.H k a/(n : ℝ)^a

def recoveredCoefficient {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (p k : ℕ) : ℂ :=
  ∑ j∈Finset.range (p+1), (multiplier n (p-j) k : ℂ)*(core M*rawActivity M j).coeff k

def approximation {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (p m : ℕ) : Polynomial ℂ :=
  ∑ k∈Finset.range (m+1), Polynomial.monomial k (recoveredCoefficient M p k)

lemma coefficient {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (p m k : ℕ) (hk : k≤ m) :
    (approximation M p m).coeff k=recoveredCoefficient M p k := by
  unfold approximation
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  simp [Finset.mem_range, hk]

lemma coefficient_above {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (p m k : ℕ) (hk : m<k) : (approximation M p m).coeff k=0 := by
  unfold approximation
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro a ha
  have hak : a≠k := by simp only [Finset.mem_range] at ha; omega
  simp [Polynomial.coeff_monomial, hak]

lemma scalar_split (g : ℕ → ℂ) (q : ℕ → ℂ) (r : ℂ)
    (p m : ℕ) (hpm : p≤ m) :
    r*(∑ j∈Finset.range (m+1), g j)-(∑ j∈Finset.range (p+1), q j*g j)=
      (∑ j∈Finset.range (p+1), (r-q j)*g j)+
      (∑ j∈Finset.Ico (p+1) (m+1), r*g j) := by
  rw [← Finset.sum_range_add_sum_Ico g (show p+1≤ m+1 by omega)]
  simp only [mul_add, Finset.mul_sum, sub_mul, Finset.sum_sub_distrib]
  ring

lemma scalar_bound (g : ℕ → ℂ) (q : ℕ → ℝ) (r : ℝ)
    (p m : ℕ) (hpm : p≤ m) :
    ‖(r : ℂ)*(∑ j∈Finset.range (m+1), g j)-
      (∑ j∈Finset.range (p+1), (q j : ℂ)*g j)‖≤
      (∑ j∈Finset.range (p+1), |r-q j| *‖g j‖)+
      (∑ j∈Finset.Ico (p+1) (m+1), |r| *‖g j‖) := by
  rw [scalar_split g (fun j => (q j : ℂ)) (r : ℂ) p m hpm]
  have h := (norm_add_le _ _).trans (add_le_add
    (norm_sum_le (Finset.range (p+1)) (fun j => ((r : ℂ)-(q j : ℂ))*g j))
    (norm_sum_le (Finset.Ico (p+1) (m+1)) (fun j => (r : ℂ)*g j)))
  simpa only [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using h

lemma coefficient_error {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hn : 0<n)
    (p m k : ℕ) (hpm : p≤ m) (hk : k≤ m) (hkn : k≤n) :
    ‖(normalized M).coeff k-(approximation M p m).coeff k‖≤
      (∑ j∈Finset.range (p+1), |factorialRecoveryRatio n k-multiplier n (p-j) k| *
        ‖(core M*rawActivity M j).coeff k‖)+
      (∑ j∈Finset.Ico (p+1) (m+1), factorialRecoveryRatio n k*
        ‖(core M*rawActivity M j).coeff k‖) := by
  rw [coefficient M p m k hk, PermanentCoreFiniteRecovery.exact_coefficient M hn m k hk, map_sum]
  have h := scalar_bound (fun j => (core M*rawActivity M j).coeff k)
    (fun j => multiplier n (p-j) k) (factorialRecoveryRatio n k) p m hpm
  simpa only [recoveredCoefficient, abs_of_pos (factorialRecoveryRatio_pos n k hn hkn)] using h

/-- Low-degree error splits into low-activity multiplier error and the true
rho-weighted high-activity mass. -/
theorem finite_window_error {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hn : 0<n)
    (p m : ℕ) (hpm : p≤ m) (hmn : m≤n) :
    (∑ k∈Finset.range (m+1), ‖(normalized M).coeff k-(approximation M p m).coeff k‖)≤
      (∑ j∈Finset.range (p+1), ActivityFactorialMultiplier.error n (p-j)
        (core M*rawActivity M j) (Finset.range (m+1)) 1)+
      (∑ j∈Finset.Ico (p+1) (m+1), ∑ k∈Finset.range (m+1),
        factorialRecoveryRatio n k*‖(core M*rawActivity M j).coeff k‖) := by
  calc
    _ ≤ ∑ k∈Finset.range (m+1),
        ((∑ j∈Finset.range (p+1), |factorialRecoveryRatio n k-multiplier n (p-j) k| *
          ‖(core M*rawActivity M j).coeff k‖)+
        (∑ j∈Finset.Ico (p+1) (m+1), factorialRecoveryRatio n k*
          ‖(core M*rawActivity M j).coeff k‖)) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkm : k≤ m := by simpa using hk
      exact coefficient_error M hn p m k hpm hkm (hkm.trans hmn)
    _ = _ := by
      rw [Finset.sum_add_distrib]
      congr 1
      · rw [Finset.sum_comm]
        simp only [ActivityFactorialMultiplier.error, multiplier, one_pow, mul_one]
      · rw [Finset.sum_comm]

lemma polynomial_tail (P : Polynomial ℂ) (n m : ℕ)
    (hP : ∀ k, n<k → P.coeff k=0) :
    (∑ k∈Finset.Ico (m+1) (n+1), ‖P.coeff k‖)=
      ∑ k∈P.support.filter (fun k => m<k), ‖P.coeff k‖ := by
  classical
  symm
  apply Finset.sum_subset
  · intro k hk
    have hh := Finset.mem_filter.mp hk
    have hk0 : P.coeff k≠0 := Polynomial.mem_support_iff.mp hh.1
    have hkn : k≤n := by by_contra h; exact hk0 (hP k (by omega))
    simp only [Finset.mem_Ico]
    omega
  · intro k hk hnot
    have hkm : m<k := by simp only [Finset.mem_Ico] at hk; omega
    have hk0 : P.coeff k=0 := by
      by_contra h
      exact hnot (Finset.mem_filter.mpr ⟨Polynomial.mem_support_iff.mpr h, hkm⟩)
    rw [hk0, norm_zero]

/-- The approximating polynomial is exactly zero above the chosen cutoff. -/
theorem full_coefficient_split {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (p m : ℕ) (hmn : m≤n) :
    (∑ k∈Finset.range (n+1), ‖(normalized M).coeff k-(approximation M p m).coeff k‖)=
      (∑ k∈Finset.range (m+1), ‖(normalized M).coeff k-(approximation M p m).coeff k‖)+
      (∑ k∈(normalized M).support.filter (fun k => m<k), ‖(normalized M).coeff k‖) := by
  rw [← Finset.sum_range_add_sum_Ico
    (fun k => ‖(normalized M).coeff k-(approximation M p m).coeff k‖)
    (show m+1≤n+1 by omega)]
  congr 1
  calc
    _ = ∑ k∈Finset.Ico (m+1) (n+1), ‖(normalized M).coeff k‖ := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkm : m<k := by simp only [Finset.mem_Ico] at hk; omega
      rw [coefficient_above M p m k hkm, sub_zero]
    _ = _ := polynomial_tail _ n m (fun k hk => coefficient_zero_above M k hk)

lemma difference_above {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (p m k : ℕ) (hmn : m≤n) (hk : n<k) :
    ((normalized M)-(approximation M p m)).coeff k=0 := by
  rw [Polynomial.coeff_sub, coefficient_zero_above M k hk,
    coefficient_above M p m k (lt_of_le_of_lt hmn hk), sub_self]

/-- A global coefficient error bound gives uniform evaluation error on the
closed unit disk, for this finite approximating polynomial. -/
theorem eval_error_le_coefficients {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (p m : ℕ) (hmn : m≤n) (z : ℂ) (hz : ‖z‖≤1) :
    ‖(normalized M).eval z-(approximation M p m).eval z‖≤
      ∑ k∈Finset.range (n+1), ‖(normalized M).coeff k-(approximation M p m).coeff k‖ := by
  have hdeg : ((normalized M)-(approximation M p m)).natDegree≤n :=
    Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (fun k hk => difference_above M p m k hmn hk)
  rw [← Polynomial.eval_sub, Polynomial.eval_eq_sum_range' (by omega :
    ((normalized M)-(approximation M p m)).natDegree<n+1)]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  rw [norm_mul, norm_pow, Polynomial.coeff_sub]
  have hp : ‖z‖^k≤1 := by simpa using pow_le_pow_left₀ (norm_nonneg z) hz k
  exact (mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans_eq (mul_one _)

end PermanentTruncatedRecoveryAlgebra
#print axioms PermanentTruncatedRecoveryAlgebra.finite_window_error
#print axioms PermanentTruncatedRecoveryAlgebra.full_coefficient_split
#print axioms PermanentTruncatedRecoveryAlgebra.eval_error_le_coefficients
