import PermanentFrozenCoefficientBridge
import PermanentCircleCentering

/-! Exact normalization of the actual permanent polynomial. No analytic
assumptions, positivity assumptions on M, or coefficient identification premises. -/
noncomputable section
namespace PermanentNormalizedFrozenBridge
open PermanentPolynomialCircleTail PermanentFrozenCoefficientBridge
open FrozenPartialPairingPolynomial PermanentSubsetMinorBridge

def normalized {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : Polynomial ℂ :=
  Polynomial.C ((n : ℂ)^n/(n.factorial : ℂ)) *
    permanentPolynomial (PermanentSpectralFrame.averaging n) M

lemma factorial_ratio (n k : ℕ) (hk : k ≤ n) :
    ((n-k).factorial : ℂ)/(n.factorial : ℂ) = 1/(n.descFactorial k : ℂ) := by
  have hn : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hd : (n.descFactorial k : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.descFactorial_pos.mpr hk))
  field_simp
  exact_mod_cast Nat.factorial_mul_descFactorial hk

lemma scalar_normalization (n k : ℕ) (hn : 0 < n) (hk : k ≤ n) :
    ((n : ℂ)^n/(n.factorial : ℂ)) * ((n : ℂ)⁻¹)^(n-k) *
      ((n-k).factorial : ℂ) = (n : ℂ)^k/(n.descFactorial k : ℂ) := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hf0 : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hp : (n : ℂ)^n = (n : ℂ)^k*(n : ℂ)^(n-k) := by
    rw [← pow_add, Nat.add_sub_of_le hk]
  calc
    _ = (n : ℂ)^k * (((n-k).factorial : ℂ)/(n.factorial : ℂ)) := by
      rw [hp, inv_pow]
      field_simp
    _ = _ := by rw [factorial_ratio n k hk]; ring

/-- The actual normalized polynomial coefficient is rho times the old Fk. -/
theorem coefficient (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ)
    (hn : 0 < n) (k : ℕ) (hk : k ≤ n) :
    (normalized M).coeff k =
      (FiniteFactorialRecovery.factorialRecoveryRatio n k : ℂ) * Fk M k := by
  rw [normalized, Polynomial.coeff_C_mul]
  change ((n : ℂ)^n/(n.factorial : ℂ)) *
    (permanentPolynomial (fun _ _ => (n : ℂ)⁻¹) M).coeff k = _
  rw [coefficient_Fk]
  rw [← mul_assoc, ← mul_assoc, scalar_normalization n k hn hk]
  simp [FiniteFactorialRecovery.factorialRecoveryRatio]

theorem coefficient_zero_above {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (k : ℕ) (hk : n < k) : (normalized M).coeff k = 0 := by
  rw [normalized, Polynomial.coeff_C_mul]
  change ((n : ℂ)^n/(n.factorial : ℂ)) *
    (permanentPolynomial (fun _ _ => (n : ℂ)⁻¹) M).coeff k = 0
  rw [PermanentFrozenCoefficientBridge.coefficient_zero_above _ M k hk, mul_zero]

/-- Above n both coefficient and Fk have separately been proved zero. -/
theorem coefficient_all {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (hn : 0 < n) (k : ℕ) :
    (normalized M).coeff k =
      (FiniteFactorialRecovery.factorialRecoveryRatio n k : ℂ) * Fk M k := by
  by_cases hk : k ≤ n
  · exact coefficient n M hn k hk
  · rw [coefficient_zero_above M k (by omega), Fk_zero_above_dimension M k (by omega), mul_zero]

end PermanentNormalizedFrozenBridge

#print axioms PermanentNormalizedFrozenBridge.coefficient
#print axioms PermanentNormalizedFrozenBridge.coefficient_all
