import GeneralZerothTail
import ActualBalancedCoreDeterminantCandidate

/-! Literal dense doubly stochastic permanent recovery with explicit uniform error. -/
set_option autoImplicit false
noncomputable section
namespace GeneralBalancedPermanent
open Matrix BalancedRawData GeneralZerothTail
open ActualResidualFrozenFactorization PermanentNormalizedFrozenBridge

lemma permanent_complexify {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.permanent (ActualHessianComplex.realComplex M) = (Matrix.permanent M : ℝ) := by
  simp [Matrix.permanent, ActualHessianComplex.realComplex]

lemma normalized_eval_one {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    (normalized (centeredComplex M)).eval 1 =
      (Matrix.permanent M/((n.factorial : ℝ)/(n : ℝ)^n) : ℝ) := by
  have he : PermanentSpectralFrame.averaging n+(1 : ℂ) • centeredComplex M =
      ActualHessianComplex.realComplex M := by
    ext i j
    simp [PermanentSpectralFrame.averaging, centeredComplex,
      ActualHessianComplex.realComplex, ActualHessianFinite.P]
  rw [normalized, Polynomial.eval_mul, Polynomial.eval_C,
    PermanentPolynomialCircleTail.permanentPolynomial_eval, he, permanent_complexify]
  push_cast
  simp only [div_eq_mul_inv, _root_.mul_inv_rev, inv_pow, inv_inv]
  ring

section Actual
variable {n : ℕ} (hn : 0 < n) (M : Matrix (Fin n) (Fin n) ℝ)
variable (C q : ℝ) (hC : 0 ≤ C)
variable (hM : ∀ i j, 0 ≤ M i j) (hd : ∀ i j, M i j ≤ C/(n : ℝ))
variable (hr : ∀ i, (∑ j, M i j)=1) (hc : ∀ j, (∑ i, M i j)=1)
variable (hq0 : 0 ≤ q) (hq1 : q < 1)
variable (hN : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (M-ActualHessianFinite.P n)‖ ≤ q)
include hn hC hM hd hr hc hq0 hq1 hN

/-- Uniform normalized absolute error, with no permanent/core approximation premise. -/
theorem actual_permanent_recovery :
    |Matrix.permanent M/((n.factorial : ℝ)/(n : ℝ)^n) -
      (Real.sqrt ((1-(M-ActualHessianFinite.P n)ᵀ*(M-ActualHessianFinite.P n)).det))⁻¹| ≤
      globalConstant C q/(n : ℝ) := by
  have h := eval_error hn M C q hC hM hd hr hc hq0 hq1 hN
  have hcore := ActualBalancedCoreDeterminantCandidate.actual_core_determinant
    hn M C q hC hM hd hr hc hq0 hq1 hN
  rw [normalized_eval_one] at h
  change FormalSeriesDerivativeAtOne.eval (core (centeredComplex M)) 1 = _ at hcore
  rw [hcore, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

/-- The literal permanent and the Gaussian determinant main term have O(n!/n^(n+1)) error. -/
theorem actual_permanent_recovery_scaled :
    |Matrix.permanent M - ((n.factorial : ℝ)/(n : ℝ)^n)*
      (Real.sqrt ((1-(M-ActualHessianFinite.P n)ᵀ*(M-ActualHessianFinite.P n)).det))⁻¹| ≤
      ((n.factorial : ℝ)/(n : ℝ)^n)*(globalConstant C q/(n : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hb : 0 < (n.factorial : ℝ)/(n : ℝ)^n := by positivity
  let b : ℝ := (n.factorial : ℝ)/(n : ℝ)^n
  let L : ℝ := (Real.sqrt ((1-(M-ActualHessianFinite.P n)ᵀ*
    (M-ActualHessianFinite.P n)).det))⁻¹
  change |Matrix.permanent M-b*L| ≤ b*(globalConstant C q/(n : ℝ))
  have hb0 : b ≠ 0 := ne_of_gt hb
  calc
    _ = |b*(Matrix.permanent M/b-L)| := by
      congr 1
      rw [mul_sub, mul_div_cancel₀ _ hb0]
    _ = b*|Matrix.permanent M/b-L| := by rw [abs_mul, abs_of_pos hb]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (actual_permanent_recovery hn M C q hC hM hd hr hc hq0 hq1 hN) hb.le

end Actual
end GeneralBalancedPermanent
