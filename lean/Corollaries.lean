import Main
import WeightedAbel

namespace NonAlgebraicity

noncomputable def exponentialFormalSeries : PowerSeries ℂ :=
  PowerSeries.mk (fun n => if n = 0 then 0 else
    (maximalPathCount n : ℂ) / (n.factorial : ℂ))

theorem scaling_factor (k : ℕ) :
    2 * (1 / 2 : ℂ) ^ (k + 1) * 2 ^ k = 1 := by
  calc
    _ = (1 / 2 : ℂ) ^ k * 2 ^ k := by rw [pow_succ]; ring
    _ = 1 := by rw [← mul_pow]; norm_num

theorem exponentialFormalSeries_eq :
    exponentialFormalSeries = (2 : ℂ) • PowerSeries.rescale (1 / 2 : ℂ)
      (PowerSeries.map (algebraMap ℚ ℂ) extremalFormalSeries) := by
  ext n
  cases n with
  | zero => simp [exponentialFormalSeries, extremalFormalSeries, normalizedCoefficient]
  | succ k =>
      simp only [exponentialFormalSeries, PowerSeries.coeff_mk, Nat.succ_ne_zero,
        ↓reduceIte, PowerSeries.coeff_smul, PowerSeries.coeff_rescale,
        PowerSeries.coeff_map, extremalFormalSeries, normalizedCoefficient,
        Nat.add_one_sub_one, eq_ratCast, Rat.cast_div, Rat.cast_mul,
        Rat.cast_pow, Rat.cast_ofNat, Rat.cast_natCast, smul_eq_mul]
      symm
      calc
        _ = (2 * (1 / 2 : ℂ) ^ (k + 1) * 2 ^ k) *
            ((maximalPathCount (k + 1) : ℂ) / ((k + 1).factorial : ℂ)) := by ring
        _ = _ := by rw [scaling_factor, one_mul]

theorem extremal_exponential_generating_function_nonalgebraic
    (asymptotic : ExtremalAsymptotic) (lw : FourExponentialIndependence) :
    ¬ HasPolynomialRelation exponentialFormalSeries := by
  rw [exponentialFormalSeries_eq]
  exact exponential_gf_non_algebraic _
    (extremal_generating_function_nonalgebraic asymptotic lw)

#print axioms extremal_exponential_generating_function_nonalgebraic

theorem extremal_exponential_generating_function_transcendental
    (asymptotic : ExtremalAsymptotic) (lw : FourExponentialIndependence) :
    Transcendental (Polynomial ℂ) exponentialFormalSeries := by
  intro h
  exact extremal_exponential_generating_function_nonalgebraic asymptotic lw
    (hasPolynomialRelation_of_isAlgebraic _ h)

#print axioms extremal_exponential_generating_function_transcendental
end NonAlgebraicity
