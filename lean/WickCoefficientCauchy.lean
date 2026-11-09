import WickAnalyticDiskTransfer
import Mathlib.Analysis.Complex.Liouville

noncomputable section
namespace WickCoefficientCauchy

theorem coefficient_bound {f : ℂ → ℂ} {a : ℕ → ℂ} {s M : ℝ}
    (hf : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ a) 0)
    (hs : 0<s) (hd : DiffContOnCl ℂ f (Metric.ball 0 s))
    (hM : ∀ z∈Metric.sphere (0:ℂ) s, ‖f z‖≤M) (k : ℕ) :
    ‖a k‖≤M/s^k := by
  rw [WickAnalyticDiskTransfer.coefficient_identity hf k,norm_div,Complex.norm_natCast]
  have hfact : (0:ℝ)<k.factorial := by exact_mod_cast Nat.factorial_pos k
  apply (div_le_iff₀ hfact).mpr
  have hh := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hs hd hM
  convert hh using 1 <;> ring

theorem weighted_bound {a : ℕ → ℂ} {ρ s M : ℝ}
    (hρ : 0≤ρ) (hs : ρ<s) (hM : 0≤M) (ha : ∀ k, ‖a k‖≤M/s^k) (k : ℕ) :
    ‖a k‖*ρ^k≤M*(ρ/s)^k := by
  have hh := mul_le_mul_of_nonneg_right (ha k) (pow_nonneg hρ k)
  convert hh using 1 <;> rw [div_pow] <;> ring

theorem weighted_summable {a : ℕ → ℂ} {ρ s M : ℝ}
    (hρ : 0≤ρ) (hs : ρ<s) (hM : 0≤M) (ha : ∀ k, ‖a k‖≤M/s^k) :
    Summable (fun k => ‖a k‖*ρ^k) := by
  have hs0 : 0<s := hρ.trans_lt hs
  have hq0 : 0≤ρ/s := div_nonneg hρ hs0.le
  have hq1 : ρ/s<1 := (div_lt_one hs0).mpr hs
  apply Summable.of_nonneg_of_le (fun k => mul_nonneg (norm_nonneg _) (pow_nonneg hρ k))
    (weighted_bound hρ hs hM ha)
  exact (summable_geometric_of_lt_one hq0 hq1).mul_left M

theorem weighted_tsum_bound {a : ℕ → ℂ} {ρ s M : ℝ}
    (hρ : 0≤ρ) (hs : ρ<s) (hM : 0≤M) (ha : ∀ k, ‖a k‖≤M/s^k) :
    (∑'k, ‖a k‖*ρ^k)≤M/(1-ρ/s) := by
  have hs0 : 0<s := hρ.trans_lt hs
  have hq0 : 0≤ρ/s := div_nonneg hρ hs0.le
  have hq1 : ρ/s<1 := (div_lt_one hs0).mpr hs
  have ht := (summable_geometric_of_lt_one hq0 hq1).mul_left M
  have hh := (weighted_summable hρ hs hM ha).tsum_le_tsum (weighted_bound hρ hs hM ha) ht
  rw [tsum_mul_left,tsum_geometric_of_lt_one hq0 hq1] at hh
  simpa only [div_eq_mul_inv] using hh

end WickCoefficientCauchy
#print axioms WickCoefficientCauchy.weighted_tsum_bound
