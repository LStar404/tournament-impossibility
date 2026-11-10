import GeneralZerothWindow
import PermanentNormalizedTailBridge
import FormalSeriesDerivativeAtOne

/-! Actual polynomial tail, actual core tail and the global zeroth-order estimate. -/
set_option autoImplicit false
noncomputable section
namespace GeneralZerothTail
open Matrix WeightedCoefficientNorm BalancedRawData GeneralBalancedWeighted
open GeneralZerothWindow ActualResidualFrozenFactorization PermanentNormalizedFrozenBridge

def permanentTailConstant (C q : ℝ) : ℝ :=
  PermanentActualCircleTail.tailConstant 0 (C+1) (outerRadius q) q (cutoff C q) 1

def coreTailConstant (C q : ℝ) : ℝ :=
  WeightedPolynomialMultiplier.moment (1/innerRadius q) 1 * coreMajorant C q / cutoff C q

def globalConstant (C q : ℝ) : ℝ :=
  errorConstant C q + permanentTailConstant C q + coreTailConstant C q

/-- Spare radius and one coefficient moment suffice, including a zero cutoff degree. -/
lemma floor_tail (F : PowerSeries ℂ) (rho alpha B : ℝ) (hrho : 1 < rho)
    (halpha : 0 < alpha) (hF : Finite rho F) (hB : norm rho F ≤ B)
    (n : ℕ) (hn : 0 < n) (E : Finset ℕ)
    (hE : ∀ k ∈ E, ⌊alpha*(n : ℝ)⌋₊ < k) :
    (∑ k ∈ E, ‖F.coeff k‖) ≤
      (WeightedPolynomialMultiplier.moment (1/rho) 1*B/alpha)/(n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hrho0 : 0 < rho := zero_lt_one.trans hrho
  have hm : 0 ≤ WeightedPolynomialMultiplier.moment (1/rho) 1 :=
    tsum_nonneg (fun k => by positivity)
  have hmom : (∑ k ∈ E, (k : ℝ)*‖F.coeff k‖) ≤
      WeightedPolynomialMultiplier.moment (1/rho) 1*B := by
    have h := WeightedPolynomialMultiplier.finite_window F E 1 1 rho 1
      (by norm_num) hrho0 (by norm_num) (by simpa only [one_mul] using hrho) hF
    have hh : (∑ k ∈ E, (k : ℝ)*‖F.coeff k‖) ≤
        WeightedPolynomialMultiplier.moment (1/rho) 1*norm rho F := by
      simpa only [pow_one, one_pow, one_mul, mul_one] using h
    exact hh.trans (mul_le_mul_of_nonneg_left hB hm)
  have hcut : (alpha*(n : ℝ))*(∑ k ∈ E, ‖F.coeff k‖) ≤
      WeightedPolynomialMultiplier.moment (1/rho) 1*B := by
    rw [Finset.mul_sum]
    apply (Finset.sum_le_sum (fun k hk =>
      mul_le_mul_of_nonneg_right (Nat.lt_of_floor_lt (hE k hk)).le (norm_nonneg _))).trans hmom
  have hh : (∑ k ∈ E, ‖F.coeff k‖) ≤
      (WeightedPolynomialMultiplier.moment (1/rho) 1*B)/(alpha*(n : ℝ)) := by
    apply (le_div_iff₀ (mul_pos halpha hnR)).mpr
    simpa only [mul_comm] using hcut
  simpa only [div_div] using hh

section Actual
variable {n : ℕ} (hn : 0 < n) (M : Matrix (Fin n) (Fin n) ℝ)
variable (C q : ℝ) (hC : 0 ≤ C)
variable (hM : ∀ i j, 0 ≤ M i j) (hd : ∀ i j, M i j ≤ C/(n : ℝ))
variable (hr : ∀ i, (∑ j, M i j)=1) (hc : ∀ j, (∑ i, M i j)=1)
variable (hq0 : 0 ≤ q) (hq1 : q < 1)
variable (hN : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (M-ActualHessianFinite.P n)‖ ≤ q)
include hn hC hM hd hr hc hq0 hq1 hN

lemma polynomial_tail :
    (∑ k ∈ (normalized (centeredComplex M)).support.filter
      (fun k => degree C q n < k), ‖(normalized (centeredComplex M)).coeff k‖) ≤
      permanentTailConstant C q/(n : ℝ) := by
  classical
  have hradii := radius_data hq0 hq1
  have hR : 1 < outerRadius q := hradii.1.trans hradii.2.1
  have hrows (i : Fin n) : ‖∑ j, centeredComplex M i j‖ ≤ (0 : ℝ)/n := by
    rw [rows hn M hr i]; simp
  have hcols (j : Fin n) : ‖∑ i, centeredComplex M i j‖ ≤ (0 : ℝ)/n := by
    rw [cols hn M hc j]; simp
  have hgap := ActualHessianComplex.realComplex_gap (M-ActualHessianFinite.P n) hq0 hN
  have h := PermanentActualCircleTail.normalized_actual_tail_bound hn (centeredComplex M)
    (by norm_num : (0 : ℝ) ≤ 0) (by linarith : 0 ≤ C+1) hR hq0 (cutoff_pos C hq1)
    hrows hcols (entry hn M hM hd) hgap hradii.2.2 1
  rw [PermanentNormalizedTailBridge.support_eq _ hn]
  simp_rw [PermanentNormalizedTailBridge.coefficient_norm _ hn]
  rw [← Finset.sum_div]
  convert h using 1 <;> simp only [degree, permanentTailConstant, pow_one]
  congr 1

lemma core_tail (E : Finset ℕ) (hE : ∀ k ∈ E, degree C q n < k) :
    (∑ k ∈ E, ‖(core (centeredComplex M)).coeff k‖) ≤ coreTailConstant C q/(n : ℝ) := by
  have hu := actual_uniform_bounds hn M C q hC hM hd hr hc hq0 hq1 hN
  exact floor_tail _ (innerRadius q) (cutoff C q) (coreMajorant C q)
    hu.1 (cutoff_pos C hq1) hu.2.1.1 hu.2.1.2 n hn E hE

/-- Summability and a uniform O(1/n) coefficient bound for the actual polynomial. -/
theorem global_coefficient_error :
    Summable (fun k => ‖(normalized (centeredComplex M)).coeff k-
      (core (centeredComplex M)).coeff k‖) ∧
    (∑' k, ‖(normalized (centeredComplex M)).coeff k-
      (core (centeredComplex M)).coeff k‖) ≤ globalConstant C q/(n : ℝ) := by
  have hlo := actual_window_error hn M C q hC hM hd hr hc hq0 hq1 hN
  have hp := polynomial_tail hn M C q hC hM hd hr hc hq0 hq1 hN
  have ht := core_tail hn M C q hC hM hd hr hc hq0 hq1 hN
  have h := WeightedRecoveryClosure.global_bound (normalized (centeredComplex M))
    (core (centeredComplex M)) 0 (degree C q n)
    (errorConstant C q/(n : ℝ)) (permanentTailConstant C q/(n : ℝ))
    (coreTailConstant C q/(n : ℝ))
    (by simpa only [WeightedRecoveryClosure.coefficientError, WeightedRecoveryClosure.weight,
      pow_zero, one_mul, window] using hlo)
    (by simpa only [WeightedRecoveryClosure.weight, pow_zero, one_mul] using hp)
    (by simpa only [WeightedRecoveryClosure.weight, pow_zero, one_mul] using ht)
  have he : WeightedRecoveryClosure.coefficientError (normalized (centeredComplex M))
      (core (centeredComplex M)) 0 = fun k =>
      ‖(normalized (centeredComplex M)).coeff k-(core (centeredComplex M)).coeff k‖ := by
    funext k
    simp only [WeightedRecoveryClosure.coefficientError, WeightedRecoveryClosure.weight,
      pow_zero, one_mul]
  rw [he] at h
  simpa only [globalConstant, add_div] using h

/-- Evaluation is the same absolutely convergent core series, not a new analytic proxy. -/
theorem eval_error :
    ‖(normalized (centeredComplex M)).eval 1-
      FormalSeriesDerivativeAtOne.eval (core (centeredComplex M)) 1‖ ≤
      globalConstant C q/(n : ℝ) := by
  have hg := global_coefficient_error hn M C q hC hM hd hr hc hq0 hq1 hN
  have hu := actual_uniform_bounds hn M C q hC hM hd hr hc hq0 hq1 hN
  have hs : Summable (WeightedRecoveryClosure.coefficientError
      (normalized (centeredComplex M)) (core (centeredComplex M)) 0) := by
    change Summable (fun k => WeightedRecoveryClosure.coefficientError
      (normalized (centeredComplex M)) (core (centeredComplex M)) 0 k)
    simpa only [WeightedRecoveryClosure.coefficientError, WeightedRecoveryClosure.weight,
      pow_zero, one_mul] using hg.1
  have hb : (∑' k, WeightedRecoveryClosure.coefficientError
      (normalized (centeredComplex M)) (core (centeredComplex M)) 0 k) ≤
      globalConstant C q/(n : ℝ) := by
    simpa only [WeightedRecoveryClosure.coefficientError, WeightedRecoveryClosure.weight,
      pow_zero, one_mul] using hg.2
  have hh := (WeightedRecoveryClosure.falling_factorial_error
    (normalized (centeredComplex M)) (core (centeredComplex M)) 0 _ hs hb).2
  rw [← FormalSeriesDerivativeAtOne.polynomial_at_one,
    ← FormalSeriesDerivativeAtOne.at_one hu.1 _ hu.2.1.1] at hh
  simpa only [iteratedDeriv_zero] using hh
end Actual
end GeneralZerothTail
