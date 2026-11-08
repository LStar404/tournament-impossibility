import QRegular
import MatrixPowerSeries
import RationalLinearDescent
import RationalSeriesLimit

open Filter Topology Polynomial Matrix
open scoped BigOperators
namespace NonAlgebraicity

/-- The full rational-limit theorem: no transcendence hypothesis is assumed.
The polynomial normalization is taken only on the geometric subsequence. -/
theorem qRegular_scaled_limit_rational (q : ℕ) (hq : 2 ≤ q)
    (a : ℕ → ℚ) (k : ℕ) (L : ℂ)
    (ha : IsQRegular q (fun n => (a n : ℂ)))
    (hlim : Tendsto (fun n => ((a n / (n : ℚ)^k : ℚ) : ℂ)) atTop (𝓝 L)) :
    ∃ r : ℚ, (r : ℂ) = L := by
  obtain ⟨d, M, v, l, he⟩ := qRegular_power_representation q hq _ ha
  have hp : Tendsto (fun e : ℕ => q ^ e) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by omega)
  let B : PowerSeries ℚ := PowerSeries.mk fun e => a (q ^ e) / ((q ^ e : ℕ) : ℚ)^k
  have hB : PowerSeries.map (algebraMap ℚ ℂ) B =
      PowerSeries.mk (fun e => l ⬝ᵥ (((((q : ℂ)^k)⁻¹ • M)^e) *ᵥ v)) := by
    ext e
    simp only [B, PowerSeries.coeff_map, PowerSeries.coeff_mk]
    change ((a (q ^ e) / ((q ^ e : ℕ) : ℚ)^k : ℚ) : ℂ) = _
    simp only [Rat.cast_div, Rat.cast_pow, Rat.cast_natCast, Nat.cast_pow,
      smul_pow, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    rw [← he]
    simp only [inv_pow, ← pow_mul, Nat.mul_comm e k, div_eq_mul_inv]
    ring
  obtain ⟨P, Q, hQ, hrel⟩ := matrix_output_series_linear_relation (((q : ℂ)^k)⁻¹ • M) v l
  rw [← hB] at hrel
  obtain ⟨p, r, hr, hre⟩ := rational_linear_relation_descends B P Q hQ hrel
  apply rational_limit_of_rational_series B L _ p r hr hre
  simpa [B, Function.comp_def] using hlim.comp hp

/-- Finite limits of rational-valued q-regular sequences are rational. -/
theorem qRegular_limit_rational (q : ℕ) (hq : 2 ≤ q)
    (a : ℕ → ℚ) (L : ℂ)
    (ha : IsQRegular q (fun n => (a n : ℂ)))
    (hlim : Tendsto (fun n => (a n : ℂ)) atTop (𝓝 L)) :
    ∃ r : ℚ, (r : ℂ) = L :=
  qRegular_scaled_limit_rational q hq a 0 L ha (by simpa using hlim)

end NonAlgebraicity
#print axioms NonAlgebraicity.qRegular_scaled_limit_rational
#print axioms NonAlgebraicity.qRegular_limit_rational
