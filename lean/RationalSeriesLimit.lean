import Mathlib.RingTheory.PowerSeries.Trunc
import Main
import RationalRadial

open Filter Topology Polynomial
open scoped BigOperators
namespace NonAlgebraicity

 theorem HasSeriesValue.add {B D : PowerSeries ℚ} {z b d : ℂ}
    (hB : HasSeriesValue B z b) (hD : HasSeriesValue D z d) :
    HasSeriesValue (B + D) z (b + d) := by
  have ht : seriesTerm (B + D) z = fun n => seriesTerm B z n + seriesTerm D z n := by
    funext n
    simp [seriesTerm, add_mul]
  rw [HasSeriesValue, ht]
  exact ⟨(hB.1.add hD.1).of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => norm_add_le _ _), hB.2.add hD.2⟩

 theorem hasSeriesValue_polynomial (P : ℚ[X]) (z : ℂ) :
    HasSeriesValue ((algebraMap ℚ[X] (PowerSeries ℚ)) P) z
      (P.eval₂ (algebraMap ℚ ℂ) z) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simpa using hP.add hQ
  | monomial n a =>
    convert (hasSeriesValue_X_pow z n).smul a using 1 <;>
      simp [PowerSeries.monomial_eq_C_mul_X_pow, PowerSeries.algebraMap_apply',
        PowerSeries.smul_eq_C_mul]

 theorem linear_relation_evaluates (B : PowerSeries ℚ) (P Q : ℚ[X])
    (he : (algebraMap ℚ[X] (PowerSeries ℚ)) Q * B =
      (algebraMap ℚ[X] (PowerSeries ℚ)) P)
    {z y : ℂ} (hy : HasSeriesValue B z y) :
    Q.eval₂ (algebraMap ℚ ℂ) z * y = P.eval₂ (algebraMap ℚ ℂ) z := by
  have hs := (hasSeriesValue_polynomial Q z).mul hy
  rw [he] at hs
  exact hs.2.unique (hasSeriesValue_polynomial P z).2

 theorem rational_limit_of_rational_series (B : PowerSeries ℚ) (L : ℂ)
    (hlim : Tendsto (fun n => ((PowerSeries.coeff n B : ℚ) : ℂ)) atTop (𝓝 L))
    (P Q : ℚ[X]) (hQ : Q ≠ 0)
    (hrel : (algebraMap ℚ[X] (PowerSeries ℚ)) Q * B =
      (algebraMap ℚ[X] (PowerSeries ℚ)) P) :
    ∃ r : ℚ, (r : ℂ) = L := by
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
  apply rational_weighted_limit_of_linear_relation 1 hx hy hne Q P hQ
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
  apply linear_relation_evaluates B P Q hrel
  apply hasSeriesValue_of_bounded B C hb
  simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr.1] using hr.2

end NonAlgebraicity
#print axioms NonAlgebraicity.rational_limit_of_rational_series
