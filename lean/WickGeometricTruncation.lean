import ActualWickCoefficientBounds

noncomputable section
namespace WickGeometricTruncation

theorem shifted_bound {a : ℕ → ℂ} {ρ s M : ℝ}
    (hρ : 0 ≤ ρ) (hs : ρ < s) (hM : 0 ≤ M) (ha : ∀ k, ‖a k‖ ≤ M/s^k)
    (m k : ℕ) : ‖a (k+m)‖*ρ^(k+m) ≤ (M*(ρ/s)^m)*(ρ/s)^k := by
  have hh := WickCoefficientCauchy.weighted_bound hρ hs hM ha (k+m)
  convert hh using 1 <;> rw [pow_add] <;> ring

theorem tail_bound {a : ℕ → ℂ} {ρ s M : ℝ}
    (hρ : 0 ≤ ρ) (hs : ρ < s) (hM : 0 ≤ M) (ha : ∀ k, ‖a k‖ ≤ M/s^k)
    (m : ℕ) : Summable (fun k => ‖a (k+m)‖*ρ^(k+m)) ∧
      (∑'k, ‖a (k+m)‖*ρ^(k+m)) ≤ M*(ρ/s)^m/(1-ρ/s) := by
  have hs0 := hρ.trans_lt hs
  have hq0 : 0 ≤ ρ/s := div_nonneg hρ hs0.le
  have hq1 : ρ/s < 1 := (div_lt_one hs0).mpr hs
  have hg := (summable_geometric_of_lt_one hq0 hq1).mul_left (M*(ρ/s)^m)
  have ht : Summable (fun k => ‖a (k+m)‖*ρ^(k+m)) :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (norm_nonneg _) (pow_nonneg hρ _))
      (shifted_bound hρ hs hM ha m) hg
  refine ⟨ht,?_⟩
  have hh := ht.tsum_le_tsum (shifted_bound hρ hs hM ha m) hg
  rw [tsum_mul_left,tsum_geometric_of_lt_one hq0 hq1] at hh
  simpa only [div_eq_mul_inv] using hh

theorem remainder_bound {a : ℕ → ℂ} {ρ s M : ℝ}
    (hρ : 0 ≤ ρ) (hs : ρ < s) (hM : 0 ≤ M) (ha : ∀ k, ‖a k‖ ≤ M/s^k)
    {z F : ℂ} (hz : ‖z‖ ≤ ρ) (hF : HasSum (fun k => a k*z^k) F) (m : ℕ) :
    ‖F-∑k∈Finset.range m,a k*z^k‖ ≤ M*(ρ/s)^m/(1-ρ/s) := by
  obtain ⟨ht,hb⟩ := tail_bound hρ hs hM ha m
  have hp (k : ℕ) : ‖a (k+m)*z^(k+m)‖ ≤ ‖a (k+m)‖*ρ^(k+m) := by
    rw [norm_mul,norm_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hz _) (norm_nonneg _)
  have hn : Summable (fun k => ‖a (k+m)*z^(k+m)‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) hp ht
  have hh : HasSum (fun k => a (k+m)*z^(k+m)) (F-∑k∈Finset.range m,a k*z^k) :=
    (hasSum_nat_add_iff' m).mpr hF
  rw [← hh.tsum_eq]
  exact (norm_tsum_le_tsum_norm hn).trans ((hn.tsum_le_tsum hp ht).trans hb)

end WickGeometricTruncation
#print axioms WickGeometricTruncation.remainder_bound
