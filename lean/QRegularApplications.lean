import QRegular
import MatrixPowerSeries
import Remainder

open Filter Topology
open scoped BigOperators
namespace NonAlgebraicity

/-- Sufficient obstruction: a rational sequence with a transcendental finite limit
cannot have finite-dimensional q-kernel. No asymptotic graph theorem is hidden here. -/
theorem not_qRegular_of_transcendental_limit (q : ℕ) (hq : 2 ≤ q)
    (a : ℕ → ℚ) (L : ℂ)
    (hlim : Tendsto (fun n => (a n : ℂ)) atTop (𝓝 L))
    (hL : Transcendental ℚ L) :
    ¬ IsQRegular q (fun n => (a n : ℂ)) := by
  intro ha
  obtain ⟨d, M, v, l, he⟩ := qRegular_power_representation q hq _ ha
  have hp : Tendsto (fun e : ℕ => q ^ e) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by omega)
  have hno := nonalgebraic_of_rational_coefficients_tendsto_transcendental
    (PowerSeries.mk fun e => a (q ^ e)) L (by simpa [Function.comp_def] using hlim.comp hp) hL
  apply hno
  convert matrix_output_series_relation M v l using 1
  ext e
  simpa using he e

 theorem normalizedCoefficient_not_qRegular (q : ℕ) (hq : 2 ≤ q)
    (asymptotic : ExtremalAsymptotic) (lw : FourExponentialIndependence) :
    ¬ IsQRegular q (fun n => (normalizedCoefficient n : ℂ)) :=
  not_qRegular_of_transcendental_limit q hq _ extremalConstant asymptotic
    (extremalConstant_transcendental lw)

/-- Polynomial normalization is applied only on the geometric subsequence;
we do not assume division by n^k preserves q-regularity. -/
theorem not_qRegular_of_scaled_transcendental_limit (q : ℕ) (hq : 2 ≤ q)
    (a : ℕ → ℚ) (k : ℕ) (L : ℂ)
    (hlim : Tendsto (fun n => ((a n / (n : ℚ)^k : ℚ) : ℂ)) atTop (𝓝 L))
    (hL : Transcendental ℚ L) :
    ¬ IsQRegular q (fun n => (a n : ℂ)) := by
  intro ha
  obtain ⟨d, M, v, l, he⟩ := qRegular_power_representation q hq _ ha
  have hp : Tendsto (fun e : ℕ => q ^ e) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by omega)
  let B : PowerSeries ℚ := PowerSeries.mk fun e => a (q ^ e) / ((q ^ e : ℕ) : ℚ)^k
  have hno := nonalgebraic_of_rational_coefficients_tendsto_transcendental
    B L (by simpa [B, Function.comp_def] using hlim.comp hp) hL
  apply hno
  convert matrix_output_series_relation (((q : ℂ)^k)⁻¹ • M) v l using 1
  ext e
  simp only [B, PowerSeries.coeff_map, PowerSeries.coeff_mk]
  change ((a (q ^ e) / ((q ^ e : ℕ) : ℚ)^k : ℚ) : ℂ) = _
  simp only [Rat.cast_div,
    Rat.cast_pow, Rat.cast_natCast, Nat.cast_pow, smul_pow, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul]
  rw [← he]
  simp only [inv_pow, ← pow_mul, Nat.mul_comm e k, div_eq_mul_inv]
  ring

 theorem halfScaleRemainder_not_qRegular (q : ℕ) (hq : 2 ≤ q)
    (asymptotic : ExtremalAsymptotic) (lw : FourExponentialIndependence) :
    ¬ IsQRegular q (fun n => (halfScaleRemainder n : ℂ)) := by
  apply not_qRegular_of_scaled_transcendental_limit q hq _ 2 extremalConstant
    _ (extremalConstant_transcendental lw)
  have heq : (fun n => ((halfScaleRemainder n / (n : ℚ)^2 : ℚ) : ℂ)) =
      (fun n => (halfScaleScaled n : ℂ)) := by
    funext n
    by_cases hn : n = 0
    · subst n; simp
    · simp [halfScaleScaled, hn]
  rw [heq]
  exact halfScaleScaled_tendsto asymptotic

end NonAlgebraicity

#print axioms NonAlgebraicity.not_qRegular_of_transcendental_limit
#print axioms NonAlgebraicity.not_qRegular_of_scaled_transcendental_limit
#print axioms NonAlgebraicity.normalizedCoefficient_not_qRegular
#print axioms NonAlgebraicity.halfScaleRemainder_not_qRegular
