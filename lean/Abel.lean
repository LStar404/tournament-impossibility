import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.LinearCombination

open Filter Topology Finset
namespace NonAlgebraicity

theorem summable_of_bounded_coefficients (a : ℕ → ℂ) (C : ℝ)
    (ha : ∀ n, ‖a n‖ ≤ C) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n => a n * z ^ n) := by
  apply ((summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left C).of_norm_bounded
  intro n
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_right (ha n) (pow_nonneg (norm_nonneg z) n)

theorem difference_series_identity (a : ℕ → ℂ) (C : ℝ)
    (ha : ∀ n, ‖a n‖ ≤ C) {z : ℂ} (hz : ‖z‖ < 1) :
    (1 - z) * (∑' n, a n * z ^ n) =
      z * (∑' n, (a (n + 1) - a n) * z ^ n) + a 0 := by
  have h0 := summable_of_bounded_coefficients a C ha hz
  have h1 := summable_of_bounded_coefficients (fun n => a (n + 1)) C
    (fun n => ha (n + 1)) hz
  have hs : (∑' n, (a (n + 1) - a n) * z ^ n) =
      (∑' n, a (n + 1) * z ^ n) - ∑' n, a n * z ^ n := by
    simp_rw [sub_mul]
    exact h1.tsum_sub h0
  have ht : (∑' n, a n * z ^ n) = a 0 + z * (∑' n, a (n + 1) * z ^ n) := by
    rw [h0.tsum_eq_zero_add]
    simp only [pow_zero, mul_one]
    congr 1
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [pow_succ]
    ring
  linear_combination ht - z * hs

/-- The Abel limit needed by the paper, with no monotonicity or rate assumption. -/
theorem abel_coefficient_limit (a : ℕ → ℂ) (L : ℂ)
    (ha : Tendsto a atTop (𝓝 L)) :
    Tendsto (fun r : ℝ => (1 - (r : ℂ)) * ∑' n, a n * (r : ℂ) ^ n)
      (𝓝[<] 1) (𝓝 L) := by
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto a ha).exists_norm_le
  have hb : ∀ n, ‖a n‖ ≤ C := fun n => hC _ ⟨n, rfl⟩
  have hd : Tendsto (fun n => ∑ i ∈ range n, (a (i + 1) - a i))
      atTop (𝓝 (L - a 0)) := by
    simpa only [Finset.sum_range_sub] using ha.sub_const (a 0)
  have hs := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt hd
  rw [tendsto_map'_iff] at hs
  have hx : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[<] 1) (𝓝 (1 : ℂ)) := by
    exact_mod_cast (Complex.continuous_ofReal.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
  have ht := (hx.mul hs).add_const (a 0)
  simp only [one_mul, sub_add_cancel] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr hpos
  exact (difference_series_identity a C hb
    (by simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos.1] using hr)).symm

#print axioms abel_coefficient_limit
end NonAlgebraicity
