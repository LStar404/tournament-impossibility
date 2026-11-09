import ActualGraphCoreRecovery
import PermanentTruncatedRecoveryAlgebra

/-! Fixed k^ell coefficient weights
for the same actual factorial multiplier. No radius strengthening is assumed. -/
noncomputable section
namespace WeightedRecoveryMultiplier
open WeightedCoefficientNorm FiniteFactorialRecovery RecoveryFiniteOrderRemainder
open PermanentTruncatedRecoveryAlgebra

def error (n q ell : ℕ) (F : PowerSeries ℂ) (E : Finset ℕ) : ℝ :=
  ∑ k∈E, |factorialRecoveryRatio n k-multiplier n q k| * (k : ℝ)^ell*‖F.coeff k‖

lemma finite_bound (n q ell : ℕ) (hn : 0<n) (F : PowerSeries ℂ) (E : Finset ℕ)
    (hF : Finite (9/8) F)
    (hE : ∀ k∈E, 2*k≤n ∧ (k : ℝ)/(n : ℝ)≤Real.log (17/16)) :
    error n q ell F E≤
      (WeightedPolynomialMultiplier.moment (17/18) (2*(q+1)+ell)/(n : ℝ)^(q+1))*norm (9/8) F := by
  unfold error multiplier
  calc
    _ ≤ ∑ k∈E, (1/(n : ℝ)^(q+1))*
        ((k : ℝ)^(2*(q+1)+ell)*(17/16 : ℝ)^k*‖F.coeff k‖*1^k) := by
      apply Finset.sum_le_sum
      intro k hk
      have hw := hE k hk
      have he := remainder n k q hn (by omega)
      have hp := factorialRecoveryRatio_le_pow n k hn hw.1 (17/16) (by norm_num) hw.2
      have hb := he.2.trans (mul_le_mul_of_nonneg_right hp
        (show 0≤((k : ℝ)^2/(n : ℝ))^(q+1) by positivity))
      have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb
        (pow_nonneg (Nat.cast_nonneg k) ell)) (norm_nonneg (F.coeff k))
      rw [abs_of_nonneg he.1]
      convert hh using 1 <;> simp only [multiplier, div_pow, pow_mul, pow_add, one_pow] <;> ring
    _ = (1/(n : ℝ)^(q+1))*(∑ k∈E,
        (k : ℝ)^(2*(q+1)+ell)*(17/16 : ℝ)^k*‖F.coeff k‖*1^k) := by rw [Finset.mul_sum]
    _ ≤ (1/(n : ℝ)^(q+1))*(WeightedPolynomialMultiplier.moment (17/18)
        (2*(q+1)+ell)*norm (9/8) F) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [mul_one, show (17/16 : ℝ)/(9/8)=17/18 by norm_num] using
        WeightedPolynomialMultiplier.finite_window F E (2*(q+1)+ell)
          1 (9/8) (17/16) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hF
    _ = _ := by ring

lemma order_bound (n p j ell : ℕ) (hn : 0<n) (hj : j≤p)
    (F : PowerSeries ℂ) (E : Finset ℕ) (L : ℝ) (hF : Finite (9/8) F)
    (hb : norm (9/8) F≤L/(n : ℝ)^j)
    (hE : ∀ k∈E, 2*k≤n ∧ (k : ℝ)/(n : ℝ)≤Real.log (17/16)) :
    error n (p-j) ell F E≤
      WeightedPolynomialMultiplier.moment (17/18) (2*(p-j+1)+ell)*L/(n : ℝ)^(p+1) := by
  have h := finite_bound n (p-j) ell hn F E hF hE
  have hm : 0≤WeightedPolynomialMultiplier.moment (17/18) (2*(p-j+1)+ell) :=
    tsum_nonneg (fun k => by positivity)
  apply h.trans
  calc
    _ ≤ (WeightedPolynomialMultiplier.moment (17/18) (2*(p-j+1)+ell)/(n : ℝ)^(p-j+1))*
        (L/(n : ℝ)^j) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by rw [div_mul_div_comm, ← pow_add, show p-j+1+j=p+1 by omega]

lemma recovered_window (n ell : ℕ) (hn : 0<n) (F : PowerSeries ℂ) (E : Finset ℕ)
    (hF : Finite (9/8) F)
    (hE : ∀ k∈E, 2*k≤n ∧ (k : ℝ)/(n : ℝ)≤Real.log (17/16)) :
    (∑ k∈E, factorialRecoveryRatio n k*(k : ℝ)^ell*‖F.coeff k‖)≤
      WeightedPolynomialMultiplier.moment (17/18) ell*norm (9/8) F := by
  calc
    _ ≤ ∑ k∈E, (k : ℝ)^ell*(17/16 : ℝ)^k*‖F.coeff k‖*1^k := by
      apply Finset.sum_le_sum
      intro k hk
      have hb := factorialRecoveryRatio_le_pow n k hn (hE k hk).1 (17/16)
        (by norm_num) (hE k hk).2
      have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb
        (pow_nonneg (Nat.cast_nonneg k) ell)) (norm_nonneg (F.coeff k))
      convert hh using 1 <;> simp only [one_pow] <;> ring
    _ ≤ _ := by
      simpa only [mul_one, show (17/16 : ℝ)/(9/8)=17/18 by norm_num] using
        WeightedPolynomialMultiplier.finite_window F E ell 1 (9/8) (17/16)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) hF

lemma window_error {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hn : 0<n)
    (p m ell : ℕ) (hpm : p≤ m) (hmn : m≤n) :
    (∑ k∈Finset.range (m+1), (k : ℝ)^ell*‖(PermanentNormalizedFrozenBridge.normalized M).coeff k-
      recoveredCoefficient M p k‖)≤
      (∑ j∈Finset.range (p+1), error n (p-j) ell
        (ActualResidualFrozenFactorization.core M*BinaryGraphActivityBound.rawActivity M j) (Finset.range (m+1)))+
      (∑ j∈Finset.Ico (p+1) (m+1), ∑ k∈Finset.range (m+1), factorialRecoveryRatio n k*(k : ℝ)^ell*
        ‖(ActualResidualFrozenFactorization.core M*BinaryGraphActivityBound.rawActivity M j).coeff k‖) := by
  calc
    _ ≤ ∑ k∈Finset.range (m+1),
        ((∑ j∈Finset.range (p+1), |factorialRecoveryRatio n k-multiplier n (p-j) k| *
          (k : ℝ)^ell*‖(ActualResidualFrozenFactorization.core M*BinaryGraphActivityBound.rawActivity M j).coeff k‖)+
        (∑ j∈Finset.Ico (p+1) (m+1), factorialRecoveryRatio n k*(k : ℝ)^ell*
          ‖(ActualResidualFrozenFactorization.core M*BinaryGraphActivityBound.rawActivity M j).coeff k‖)) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkm : k≤ m := by simpa using hk
      have h := PermanentTruncatedRecoveryAlgebra.coefficient_error M hn p m k hpm hkm (hkm.trans hmn)
      rw [PermanentTruncatedRecoveryAlgebra.coefficient M p m k hkm] at h
      have hh := mul_le_mul_of_nonneg_left h (pow_nonneg (Nat.cast_nonneg k) ell)
      convert hh using 1 <;>
        simp only [mul_add, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
    _ = _ := by
      rw [Finset.sum_add_distrib]
      congr 1
      · rw [Finset.sum_comm]
        rfl
      · rw [Finset.sum_comm]

end WeightedRecoveryMultiplier
#print axioms WeightedRecoveryMultiplier.order_bound
#print axioms WeightedRecoveryMultiplier.recovered_window
