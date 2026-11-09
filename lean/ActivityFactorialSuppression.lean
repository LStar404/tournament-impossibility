import OrderedResidualPolynomial
import Mathlib.Analysis.Complex.Exponential

noncomputable section
namespace ActivityFactorialSuppression

theorem logarithm_norm (d : ℕ) :
    ‖(ResidualLogarithm.logarithm (S:=ℂ)).coeff d‖ ≤ 1 := by
  rcases d with _ | _ | _ | d
  · norm_num [ResidualLogarithm.logarithm]
  · norm_num [ResidualLogarithm.logarithm]
  · norm_num [ResidualLogarithm.logarithm]
  · simp only [ResidualLogarithm.logarithm,PowerSeries.coeff_mk,norm_div,norm_pow,
      norm_neg,norm_one,one_pow,Complex.norm_natCast]
    rw [show (d:ℂ)+3=((d+3:ℕ):ℂ) by push_cast; rfl,Complex.norm_natCast]
    apply (div_le_one (by positivity)).mpr
    push_cast; linarith [Nat.cast_nonneg (α:=ℝ) d]

theorem scalar_norm {b : ℕ} (d : Fin b →₀ ℕ) :
    ‖OrderedResidualPolynomial.scalar (S:=ℂ) d‖ ≤ 1/(b.factorial:ℝ) := by
  have hp : ‖∏v:Fin b,(ResidualLogarithm.logarithm (S:=ℂ)).coeff (d v)‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => logarithm_norm _)
  unfold OrderedResidualPolynomial.scalar
  rw [norm_mul]
  have hc : ‖algebraMap ℚ ℂ (1/(b.factorial:ℚ))‖=1/(b.factorial:ℝ) := by
    simp [map_div]
  rw [hc]
  simpa using mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 1/(b.factorial:ℝ))

/-- This retains the vertex factorial: dropping it loses the desired j^j scale. -/
theorem suppression (j b e : ℕ) (hj : 1 ≤ j) (he : e ≤ j+b) :
    (j:ℝ)^e/(b.factorial:ℝ) ≤ (j:ℝ)^j*Real.exp (j:ℝ) := by
  have hjR : (1:ℝ) ≤ j := by exact_mod_cast hj
  calc
    _ ≤ (j:ℝ)^(j+b)/(b.factorial:ℝ) :=
      div_le_div_of_nonneg_right (pow_le_pow_right₀ hjR he) (by positivity)
    _ = (j:ℝ)^j*((j:ℝ)^b/(b.factorial:ℝ)) := by rw [pow_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.pow_div_factorial_le_exp (j:ℝ) (Nat.cast_nonneg j) b) (by positivity)

/-- Exact dimension cancellation, before any combinatorial overestimate. -/
theorem dimension_cancel (n b e h j : ℕ) (hn : 0<n) (he : e+h=j+b) :
    ((2*(n:ℝ))^b)/(n:ℝ)^(e+h)=(2:ℝ)^b/(n:ℝ)^j := by
  rw [he,pow_add,mul_pow]
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp
end ActivityFactorialSuppression
#print axioms ActivityFactorialSuppression.scalar_norm
#print axioms ActivityFactorialSuppression.suppression
