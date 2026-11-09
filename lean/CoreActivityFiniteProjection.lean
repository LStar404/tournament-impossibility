import BinaryGraphActivityBound
import ActivityZeroNormalization
import PermanentSubsetMinorBridge

/-! Exact finite projection of the original frozen polynomial into core times
the actual finite activities. No infinite-j analytic sum is formed. -/
noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace CoreActivityFiniteProjection
open BinaryGraphActivityBound ActualResidualFrozenFactorization
open FrozenPartialPairingPolynomial

lemma index_below {I S : Type*} [Fintype I] [Field S] [CharZero S] [Algebra ℚ S]
    (K A : I → I → S) (hK : ∀ i j, K i j=K j i)
    (hA : ∀ i j, A i j=A j i) (h : I → S)
    (m k j : ℕ) (hkj : k < j) :
    GlobalActivityFiniteRegroup.byIndex K A hK hA h m k j = 0 := by
  unfold GlobalActivityFiniteRegroup.byIndex
  apply Finset.sum_eq_zero
  intro b hb
  apply Finset.sum_eq_zero
  intro a ha
  apply Finset.sum_eq_zero
  intro d hd
  split_ifs with hdeg
  · have hsum : (∑ v, d v) = m := (Finset.mem_finsuppAntidiag.mp hd).1
    have hz := GlobalActivityFiniteRegroup.activity_constraints K A hK hA h d
      hdeg a m k j hsum (by omega)
    rw [hz, mul_zero]
  · rfl

theorem activity_below {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (j k : ℕ) (hkj : k < j) : (rawActivity M j).coeff k = 0 := by
  unfold rawActivity
  rw [ActualFiniteActivity.coefficient]
  exact Finset.sum_eq_zero (fun m hm => index_below _ _ _ _ _ m k j hkj)

theorem product_below {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (j k : ℕ) (hkj : k < j) : (core M * rawActivity M j).coeff k = 0 := by
  rw [PowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro ab hab
  have hh := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
  rw [activity_below M j ab.2 (by omega), mul_zero]

theorem residual_truncated {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (m k : ℕ) (hk : k ≤ m) :
    (residualZ M).coeff k =
      (∑ j ∈ Finset.range (m+1), rawActivity M j).coeff k := by
  rw [ActualFiniteActivity.actual_residual, map_sum]
  change (∑ j ∈ Finset.range (k+1), (rawActivity M j).coeff k) = _
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro j hj hnot
  exact activity_below M j k (by simpa using hnot)

theorem frozen_coefficient {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    ((frozenPolynomial M : PowerSeries ℂ)).coeff k = Fk M k := by
  rw [Polynomial.coeff_coe]
  unfold frozenPolynomial
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  by_cases hk : k ≤ n
  · simp [Finset.mem_range, hk]
  · rw [PermanentSubsetMinorBridge.Fk_zero_above_dimension M k (by omega)]
    apply Finset.sum_eq_zero
    intro a ha
    simp only [Finset.mem_range] at ha
    simp [show a ≠ k by omega]

/-- The low-degree coefficients of the independent frozen polynomial agree
with a FINITE sum of true core-activity products. -/
theorem coefficient_projection {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (m k : ℕ) (hk : k ≤ m) :
    Fk M k = (∑ j ∈ Finset.range (m+1), core M * rawActivity M j).coeff k := by
  rw [← frozen_coefficient M k, polynomial_factorization, ← Finset.mul_sum]
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro ab hab
  have hh := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
  rw [residual_truncated M m ab.2 (by omega)]

theorem zero_activity_product {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    core M * rawActivity M 0 = core M := by
  have hz : rawActivity M 0 = 1 := ActivityZeroNormalization.zero _ _ _ _ _
  rw [hz, mul_one]

end CoreActivityFiniteProjection

#print axioms CoreActivityFiniteProjection.coefficient_projection
#print axioms CoreActivityFiniteProjection.activity_below
