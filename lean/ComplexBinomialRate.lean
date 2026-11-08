import DiamondFreeKernelUniform

noncomputable section
namespace ComplexBinomialRate
open Complex

lemma log_remainder_half (u : ℂ) (hu : ‖u‖ ≤ 1/2) :
    ‖Complex.log (1+u)-u‖ ≤ ‖u‖^2 := by
  have hp : 0 < 1-‖u‖ := by linarith
  have hi : (1-‖u‖)⁻¹ ≤ 2 := by
    have h := inv_anti₀ (show (0:ℝ)<1/2 by norm_num) (show (1:ℝ)/2 ≤ 1-‖u‖ by linarith)
    norm_num at h
    exact h
  have h := Complex.norm_log_one_add_sub_self_le (show ‖u‖ < 1 by linarith)
  have hm := mul_le_mul_of_nonneg_left hi (sq_nonneg ‖u‖)
  linarith

lemma scaled_log_error (n : ℕ) (hn : 0<n) (w : ℂ)
    (hw : ‖w‖/(n:ℝ) ≤ 1/2) :
    ‖(n:ℂ)*Complex.log (1+w/(n:ℂ))-w‖ ≤ ‖w‖^2/(n:ℝ) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hnC : (n:ℂ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  have he : (n:ℂ)*Complex.log (1+w/(n:ℂ))-w =
      (n:ℂ)*(Complex.log (1+w/(n:ℂ))-w/(n:ℂ)) := by field_simp
  rw [he, norm_mul, Complex.norm_natCast]
  have hu : ‖w/(n:ℂ)‖ ≤ 1/2 := by simpa using hw
  calc
    _ ≤ (n:ℝ)*‖w/(n:ℂ)‖^2 := mul_le_mul_of_nonneg_left (log_remainder_half _ hu) hnR.le
    _ = ‖w‖^2/(n:ℝ) := by simp only [norm_div, Complex.norm_natCast]; field_simp

/-- An explicit uniform-on-balls binomial bound once both smallness conditions
hold. This is quantitative, unlike the earlier compact convergence theorem. -/
theorem binomial_error (n : ℕ) (hn : 0<n) (w : ℂ) (R : ℝ)
    (hwR : ‖w‖≤R) (hsmall : R/(n:ℝ)≤1/2) (herr : R^2/(n:ℝ)≤1) :
    ‖(1+w/(n:ℂ))^n-Complex.exp w‖ ≤ 2*Real.exp R*R^2/(n:ℝ) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hR : 0≤R := (norm_nonneg w).trans hwR
  have hw : ‖w‖/(n:ℝ)≤1/2 := (div_le_div_of_nonneg_right hwR hnR.le).trans hsmall
  let e : ℂ := (n:ℂ)*Complex.log (1+w/(n:ℂ))-w
  have he : ‖e‖≤R^2/(n:ℝ) := (scaled_log_error n hn w hw).trans
    (div_le_div_of_nonneg_right (sq_le_sq₀ (norm_nonneg _) hR |>.2 hwR) hnR.le)
  have hzero : 1+w/(n:ℂ)≠0 := by
    intro hz
    have hnorm : ‖w/(n:ℂ)‖=1 := by
      have hh : w/(n:ℂ)= -1 := by linear_combination hz
      simp [hh]
    have hu : ‖w/(n:ℂ)‖≤1/2 := by simpa using hw
    linarith
  have hid : (1+w/(n:ℂ))^n-Complex.exp w =
      Complex.exp w*(Complex.exp e-1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    dsimp [e]
    rw [add_sub_cancel, Complex.exp_nat_mul, Complex.exp_log hzero]
  rw [hid, norm_mul]
  calc
    _ ≤ Real.exp R * (2*‖e‖) := mul_le_mul
      ((Complex.norm_exp_le_exp_norm w).trans (Real.exp_le_exp.mpr hwR))
      (Complex.norm_exp_sub_one_le (he.trans herr)) (norm_nonneg _) (Real.exp_pos R).le
    _ ≤ Real.exp R * (2*(R^2/(n:ℝ))) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left he (by norm_num)) (Real.exp_pos R).le
    _ = _ := by ring
theorem finiteKernel_error (n : ℕ) (hn : 0<n) (w : ℂ) (R : ℝ)
    (hwR : ‖w‖≤R) (hsmall : R/(n:ℝ)≤1/2) (herr : R^2/(n:ℝ)≤1) :
    ‖DiamondFreeKernelLimit.finiteKernel n w-Complex.cosh w‖ ≤ 2*Real.exp R*R^2/(n:ℝ) := by
  have hp := binomial_error n hn w R hwR hsmall herr
  have hm := binomial_error n hn (-w) R (by simpa using hwR) hsmall herr
  have hid : DiamondFreeKernelLimit.finiteKernel n w-Complex.cosh w =
      (((1+w/(n:ℂ))^n-Complex.exp w)+((1+(-w)/(n:ℂ))^n-Complex.exp (-w)))/2 := by
    unfold DiamondFreeKernelLimit.finiteKernel Complex.cosh
    simp only [neg_div, sub_eq_add_neg]
    ring
  rw [hid, norm_div]
  norm_num only [Complex.norm_ofNat]
  have ha := norm_add_le ((1+w/(n:ℂ))^n-Complex.exp w)
    ((1+(-w)/(n:ℂ))^n-Complex.exp (-w))
  linarith

theorem actual_imaginary_error {n : ℕ} (T : DiamondGap.Tournament (Fin n))
    (hT : T.diamonds.card=0) (hn : 0<n) (w : ℂ) (R : ℝ)
    (hwR : ‖w‖≤R) (hsmall : R/(n:ℝ)≤1/2) (herr : R^2/(n:ℝ)≤1) :
    ‖(DiamondFreeKernelDeterminant.kernel T (w*Complex.I/(n:ℂ))).det-Complex.cos w‖
      ≤ 2*Real.exp R*R^2/(n:ℝ) := by
  have h := finiteKernel_error n hn (w*Complex.I) R (by simpa using hwR) hsmall herr
  rw [DiamondFreeKernelDeterminant.zero_diamonds_kernel_det T hT]
  simpa [DiamondFreeKernelLimit.finiteKernel, Complex.cosh_mul_I] using h

end ComplexBinomialRate
#print axioms ComplexBinomialRate.binomial_error

#print axioms ComplexBinomialRate.actual_imaginary_error
