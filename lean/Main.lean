import Application
import Evaluation
import Radial
import Normalization
import StandardAlgebraicity

open Filter Topology
namespace NonAlgebraicity

theorem hasSeriesValue_of_bounded (B : PowerSeries ℚ) (C : ℝ)
    (hB : ∀ n, ‖((PowerSeries.coeff n B : ℚ) : ℂ)‖ ≤ C)
    {z : ℂ} (hz : ‖z‖ < 1) :
    HasSeriesValue B z (∑' n, seriesTerm B z n) := by
  have hs : Summable (fun n => ‖seriesTerm B z n‖) := by
    apply ((summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left C).of_norm_bounded
    intro n
    simp only [seriesTerm, norm_norm, norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_right (hB n) (pow_nonneg (norm_nonneg z) n)
  exact ⟨hs, hs.of_norm.hasSum⟩

noncomputable def extremalFormalSeries : PowerSeries ℚ :=
  PowerSeries.mk normalizedCoefficient

/-- A rational-coefficient series whose coefficients tend to a transcendental
number has no nonzero polynomial relation even over the complex numbers. -/
theorem nonalgebraic_of_rational_coefficients_tendsto_transcendental
    (B : PowerSeries ℚ) (L : ℂ)
    (hlim : Tendsto (fun n => ((PowerSeries.coeff n B : ℚ) : ℂ)) atTop (𝓝 L))
    (hL : Transcendental ℚ L) :
    ¬ HasPolynomialRelation (PowerSeries.map (algebraMap ℚ ℂ) B) := by
  intro hrel
  obtain ⟨m, n, c, hc, he⟩ := rational_polynomial_relation_descends B hrel
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto _ hlim).exists_norm_le
  have hb : ∀ n, ‖((PowerSeries.coeff n B : ℚ) : ℂ)‖ ≤ C := fun n => hC _ ⟨n, rfl⟩
  have hx : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[<] 1) (𝓝 (1 : ℂ)) := by
    exact_mod_cast (Complex.continuous_ofReal.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
  have hne : ∀ᶠ r : ℝ in 𝓝[<] 1, (r : ℂ) ≠ 1 := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact_mod_cast (ne_of_lt hr)
  have hy : Tendsto (fun r : ℝ => (1 - (r : ℂ)) ^ 1 * ∑' k, seriesTerm B r k)
      (𝓝[<] 1) (𝓝 L) := by
    simpa only [pow_one, seriesTerm] using abel_coefficient_limit _ _ hlim
  have hp : ∀ᶠ r : ℝ in 𝓝[<] 1,
      evalXY (arrayPolynomial c) r (∑' k, seriesTerm B r k) = 0 := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
    rw [evalXY, arrayPolynomial_eval]
    apply relation_evaluates_zero B c he
    apply hasSeriesValue_of_bounded B C hb
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr.1] using hr.2
  exact hL (algebraic_weighted_limit_of_relation 1 hx hy hne
    (arrayPolynomial c) (arrayPolynomial_ne_zero c hc) hp)

/-- Main application. The graph asymptotic and finite Lindemann--Weierstrass
input are explicit hypotheses. Every intervening step is checked by Lean. -/
theorem extremal_generating_function_nonalgebraic
    (asymptotic : ExtremalAsymptotic) (lw : FourExponentialIndependence) :
    ¬ HasPolynomialRelation (PowerSeries.map (algebraMap ℚ ℂ) extremalFormalSeries) := by
  unfold ExtremalAsymptotic at asymptotic
  apply nonalgebraic_of_rational_coefficients_tendsto_transcendental
    extremalFormalSeries extremalConstant
  · simpa only [extremalFormalSeries, PowerSeries.coeff_mk] using asymptotic
  · exact extremalConstant_transcendental lw

#print axioms nonalgebraic_of_rational_coefficients_tendsto_transcendental
#print axioms extremal_generating_function_nonalgebraic

/-- Standard mathlib formulation: clearing rational-function denominators
makes transcendence over C(z) equivalent to transcendence over C[X]. -/
theorem extremal_generating_function_transcendental
    (asymptotic : ExtremalAsymptotic) (lw : FourExponentialIndependence) :
    Transcendental (Polynomial ℂ)
      (PowerSeries.map (algebraMap ℚ ℂ) extremalFormalSeries) := by
  intro h
  exact extremal_generating_function_nonalgebraic asymptotic lw
    (hasPolynomialRelation_of_isAlgebraic _ h)

#print axioms extremal_generating_function_transcendental

set_option maxHeartbeats 600000 in
/-- General radial criterion: the summability of the evaluated series is supplied
by the caller, so this applies to coefficient sequences that grow polynomially. -/
theorem nonalgebraic_of_radial_limit (B : PowerSeries ℚ) (L : ℂ) (d : ℕ)
    (hsumm : ∀ r : ℝ, (0 : ℝ) < r → r < 1 →
      HasSeriesValue B (r : ℂ) (∑' k, seriesTerm B (r : ℂ) k))
    (hlim : Tendsto (fun r : ℝ => (1 - (r : ℂ)) ^ d * ∑' k, seriesTerm B (r : ℂ) k)
      (𝓝[<] 1) (𝓝 L))
    (hL : Transcendental ℚ L) :
    ¬ HasPolynomialRelation (PowerSeries.map (algebraMap ℚ ℂ) B) := by
  intro hrel
  obtain ⟨m, n, c, hc, he⟩ := rational_polynomial_relation_descends B hrel
  have hx : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[<] 1) (𝓝 (1 : ℂ)) :=
    Complex.continuous_ofReal.tendsto (1 : ℝ) |>.mono_left nhdsWithin_le_nhds
  have hne : ∀ᶠ r : ℝ in 𝓝[<] 1, (r : ℂ) ≠ 1 := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact_mod_cast (ne_of_lt hr)
  have hp : ∀ᶠ r : ℝ in 𝓝[<] 1,
      evalXY (arrayPolynomial c) r (∑' k, seriesTerm B (r : ℂ) k) = 0 := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
    rw [evalXY, arrayPolynomial_eval]
    exact relation_evaluates_zero B c he (hsumm r hr.1 hr.2)
  exact hL (algebraic_weighted_limit_of_relation d hx hlim hne
    (arrayPolynomial c) (arrayPolynomial_ne_zero c hc) hp)

#print axioms nonalgebraic_of_radial_limit

end NonAlgebraicity
