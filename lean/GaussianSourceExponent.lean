import ComplexBinomialRate

noncomputable section
namespace GaussianSourceExponent

def exponent (n : ℕ) (a k ψ : ℂ) : ℂ :=
  a/(1+a/(n:ℂ)) - k^2*(ψ/(n:ℂ)^2)/(1+a/(n:ℂ))

/-- The rational source denominator is bounded away from zero, not assumed
invertible just because Lean provides a totalized division operation. -/
theorem denominator_bound (n : ℕ) (hn : 0<n) (a : ℂ) {r : ℝ}
    (ha : ‖a‖≤r) (hsmall : r/(n:ℝ)≤1/2) :
    (1:ℝ)/2≤‖1+a/(n:ℂ)‖ ∧ 1+a/(n:ℂ)≠0 ∧ ‖(1+a/(n:ℂ))⁻¹‖≤2 := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hu : ‖a/(n:ℂ)‖≤1/2 := by
    simpa using (div_le_div_of_nonneg_right ha hnR.le).trans hsmall
  have h := norm_sub_norm_le (1:ℂ) (1+a/(n:ℂ))
  have he : (1:ℂ)-(1+a/(n:ℂ))= -(a/(n:ℂ)) := by ring
  rw [he,norm_neg,norm_one] at h
  have hl : (1:ℝ)/2≤‖1+a/(n:ℂ)‖ := by linarith
  have hz : 1+a/(n:ℂ)≠0 := by
    intro hh
    simp [hh] at hl
    linarith
  refine ⟨hl,hz,?_⟩
  rw [norm_inv]
  have hi := inv_anti₀ (show (0:ℝ)<1/2 by norm_num) hl
  norm_num at hi
  exact hi

/-- Uniform quantitative source-exponent estimate, retaining the explicit
bound on the normalized source. Graph-specific inputs are supplied elsewhere. -/
theorem exponent_error (n : ℕ) (hn : 0<n) (a k ψ : ℂ) {r R B : ℝ}
    (ha : ‖a‖≤r) (hsmall : r/(n:ℝ)≤1/2) (hk : ‖k‖≤R)
    (hB : 0≤B) (hψ : ‖ψ‖/(n:ℝ)^2≤B/(n:ℝ)) :
    ‖exponent n a k ψ-a‖≤2*(r^2+R^2*B)/(n:ℝ) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hnC : (n:ℂ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  have hr : 0≤r := (norm_nonneg a).trans ha
  have hR : 0≤R := (norm_nonneg k).trans hk
  have hd := denominator_bound n hn a ha hsmall
  have hid : exponent n a k ψ-a =
      -(a^2/(n:ℂ)+k^2*(ψ/(n:ℂ)^2))/(1+a/(n:ℂ)) := by
    apply (eq_div_iff hd.2.1).2
    unfold exponent
    rw [sub_mul,sub_mul,div_mul_cancel₀ _ hd.2.1,div_mul_cancel₀ _ hd.2.1]
    field_simp [hnC]
    <;> ring
  have hfirst : ‖a^2/(n:ℂ)‖≤r^2/(n:ℝ) := by
    simp only [norm_div,norm_pow,Complex.norm_natCast]
    exact div_le_div_of_nonneg_right ((sq_le_sq₀ (norm_nonneg a) hr).2 ha) hnR.le
  have hsecond : ‖k^2*(ψ/(n:ℂ)^2)‖≤R^2*(B/(n:ℝ)) := by
    simp only [norm_mul,norm_pow,norm_div,Complex.norm_natCast]
    exact mul_le_mul ((sq_le_sq₀ (norm_nonneg k) hR).2 hk) hψ
      (div_nonneg (norm_nonneg ψ) (sq_nonneg _)) (sq_nonneg R)
  have hnum : ‖a^2/(n:ℂ)+k^2*(ψ/(n:ℂ)^2)‖≤r^2/(n:ℝ)+R^2*(B/(n:ℝ)) :=
    (norm_add_le _ _).trans (add_le_add hfirst hsecond)
  rw [hid,div_eq_mul_inv,norm_mul,norm_neg]
  calc
    _ ≤ (r^2/(n:ℝ)+R^2*(B/(n:ℝ)))*2 := mul_le_mul hnum hd.2.2
      (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- Explicit complex exponential perturbation bound; no differentiation of
pointwise big-O notation is used. -/
theorem exp_difference (x a : ℂ) {r E : ℝ}
    (ha : ‖a‖≤r) (he : ‖x-a‖≤E) (hE : E≤1) :
    ‖Complex.exp x-Complex.exp a‖≤2*Real.exp r*E := by
  have hid : Complex.exp x-Complex.exp a =
      Complex.exp a*(Complex.exp (x-a)-1) := by
    rw [mul_sub,mul_one,← Complex.exp_add]
    congr 1
    ring
  rw [hid,norm_mul]
  calc
    _ ≤ Real.exp r*(2*‖x-a‖) := mul_le_mul
      ((Complex.norm_exp_le_exp_norm a).trans (Real.exp_le_exp.mpr ha))
      (Complex.norm_exp_sub_one_le (he.trans hE)) (norm_nonneg _) (Real.exp_pos r).le
    _ ≤ Real.exp r*(2*E) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left he (by norm_num)) (Real.exp_pos r).le
    _ = _ := by ring

theorem exp_exponent_error (n : ℕ) (hn : 0<n) (a k ψ : ℂ) {r R B : ℝ}
    (ha : ‖a‖≤r) (hsmall : r/(n:ℝ)≤1/2) (hk : ‖k‖≤R)
    (hB : 0≤B) (hψ : ‖ψ‖/(n:ℝ)^2≤B/(n:ℝ))
    (hE : 2*(r^2+R^2*B)/(n:ℝ)≤1) :
    ‖Complex.exp (exponent n a k ψ)-Complex.exp a‖≤
      4*Real.exp r*(r^2+R^2*B)/(n:ℝ) := by
  have h := exp_difference (exponent n a k ψ) a ha
    (exponent_error n hn a k ψ ha hsmall hk hB hψ) hE
  convert h using 1 <;> ring

end GaussianSourceExponent
#print axioms GaussianSourceExponent.denominator_bound
#print axioms GaussianSourceExponent.exponent_error
#print axioms GaussianSourceExponent.exp_exponent_error
