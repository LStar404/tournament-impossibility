import Main
import QuadraticAbel

/-!
# The half-scale remainder generating function

The paper's third generating function is the remainder of the half-scale
recursion, `M(z) = Σ m_n z^n` with `m_n = n^2 a_n - 2·1_{2|n}·a_{n/2}`.
Its coefficients are rational and satisfy `m_n / n^2 → L`, so the `(1-r)^3`
normalization of `QuadraticAbel` applies and the same transcendence input rules
out a polynomial relation.

The construction is split into small lemmas so that each declaration stays
within a modest elaboration budget.
-/

open Filter Topology
open scoped BigOperators

namespace NonAlgebraicity

/-- `m_n = n^2 a_n - 2·1_{2|n}·a_{n/2}`. -/
noncomputable def halfScaleRemainder (n : ℕ) : ℚ :=
  (n : ℚ) ^ 2 * normalizedCoefficient n -
    if 2 ∣ n then 2 * normalizedCoefficient (n / 2) else 0

/-- The normalized coefficient `m_n / n^2`, set to zero at `n = 0`. -/
noncomputable def halfScaleScaled (n : ℕ) : ℚ :=
  if n = 0 then 0 else halfScaleRemainder n / (n : ℚ) ^ 2

/-- The remainder generating function `M(z) = Σ m_n z^n`. -/
noncomputable def halfScaleSeries : PowerSeries ℚ := PowerSeries.mk halfScaleRemainder

@[simp] theorem halfScaleRemainder_zero : halfScaleRemainder 0 = 0 := by
  simp [halfScaleRemainder]

@[simp] theorem halfScaleScaled_zero : halfScaleScaled 0 = 0 := by
  simp [halfScaleScaled]

/-- `n^2 · (m_n / n^2) = m_n`: the normalization is exact. -/
theorem scaled_mul_sq (n : ℕ) :
    (n : ℂ) ^ 2 * ((halfScaleScaled n : ℚ) : ℂ) = ((halfScaleRemainder n : ℚ) : ℂ) := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    simp
  · have hn0 : ¬ n = 0 := by omega
    have hnq : ((n : ℚ)) ≠ 0 := by
      have hn : (n : ℕ) ≠ 0 := by omega
      exact_mod_cast hn
    have hstep : halfScaleScaled n = halfScaleRemainder n / (n : ℚ) ^ 2 := by
      unfold halfScaleScaled
      rw [if_neg hn0]
    rw [hstep]
    push_cast
    have hnc : ((n : ℂ)) ^ 2 ≠ 0 := by
      have hn : ((n : ℂ)) ≠ 0 := by exact_mod_cast hnq
      exact pow_ne_zero 2 hn
    field_simp

/-- The correction term `2·1_{2|n}·a_{n/2} / n^2`. -/
noncomputable def tailCorrection (n : ℕ) : ℂ :=
  if 2 ∣ n then 2 * ((normalizedCoefficient (n / 2) : ℚ) : ℂ) / (n : ℂ) ^ 2 else 0

set_option maxHeartbeats 600000 in
/-- The correction term tends to zero. -/
theorem tailCorrection_tendsto (h : ExtremalAsymptotic) :
    Tendsto tailCorrection atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto _ h).exists_norm_le
  have hC' : ∀ n, ‖((normalizedCoefficient n : ℚ) : ℂ)‖ ≤ C := fun n => hC _ ⟨n, rfl⟩
  have hCnn : (0 : ℝ) ≤ C := le_trans (norm_nonneg _) (hC' 0)
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun n : ℕ => (2 * C) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hnat
  have hlim : Tendsto (fun n : ℕ => (2 * C) / (n : ℝ) ^ 2) atTop (𝓝 0) := by
    have h2 : Tendsto (fun n : ℕ => ((2 * C) / (n : ℝ)) / (n : ℝ)) atTop (𝓝 0) :=
      h1.div_atTop hnat
    simpa [div_div, pow_two] using h2
  have hbound : ∀ n : ℕ, ‖tailCorrection n‖ ≤ (2 * C) / (n : ℝ) ^ 2 := by
    intro n
    by_cases hd : 2 ∣ n
    · have hnum : ‖(2 : ℂ) * ((normalizedCoefficient (n / 2) : ℚ) : ℂ)‖ ≤ 2 * C := by
        rw [norm_mul]
        have h2c : ‖(2 : ℂ)‖ = 2 := by simp
        rw [h2c]
        nlinarith [hC' (n / 2)]
      have hden2 : ‖(n : ℂ) ^ 2‖ = (n : ℝ) ^ 2 := norm_sq_natCast n
      simp only [tailCorrection, hd, if_true]
      rw [norm_div, hden2]
      exact div_le_div_of_nonneg_right hnum (sq_nonneg (n : ℝ))
    · simp only [tailCorrection, hd, if_false, norm_zero]
      have : (0 : ℝ) ≤ (2 * C) / (n : ℝ) ^ 2 := div_nonneg (by linarith) (sq_nonneg _)
      exact this
  have hzero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
  have hnorm : Tendsto (fun n => ‖tailCorrection n‖) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le (f := fun n => ‖tailCorrection n‖)
      hzero hlim (fun n => norm_nonneg _) hbound
  rwa [tendsto_zero_iff_norm_tendsto_zero]

set_option maxHeartbeats 600000 in
/-- The normalized remainder coefficients tend to `L`. -/
theorem halfScaleScaled_tendsto (h : ExtremalAsymptotic) :
    Tendsto (fun n => ((halfScaleScaled n : ℚ) : ℂ)) atTop (𝓝 extremalConstant) := by
  have hcorr := tailCorrection_tendsto h
  have hmain : Tendsto (fun n => ((normalizedCoefficient n : ℚ) : ℂ)) atTop
      (𝓝 extremalConstant) := h
  have hdiff : Tendsto (fun n => ((normalizedCoefficient n : ℚ) : ℂ) - tailCorrection n)
      atTop (𝓝 (extremalConstant - 0)) := hmain.sub hcorr
  have hEq : ∀ᶠ n : ℕ in atTop,
      ((normalizedCoefficient n : ℚ) : ℂ) - tailCorrection n = ((halfScaleScaled n : ℚ) : ℂ) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn0 : ¬ n = 0 := by omega
    have hnq : ((n : ℚ)) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]
      omega
    by_cases hd : 2 ∣ n
    · have hq : halfScaleScaled n
          = normalizedCoefficient n - 2 * normalizedCoefficient (n / 2) / (n : ℚ) ^ 2 := by
        unfold halfScaleScaled halfScaleRemainder
        rw [if_neg hn0, if_pos hd]
        field_simp
      have hcast : ((halfScaleScaled n : ℚ) : ℂ)
          = ((normalizedCoefficient n : ℚ) : ℂ)
            - 2 * ((normalizedCoefficient (n / 2) : ℚ) : ℂ) / (n : ℂ) ^ 2 := by
        rw [hq]
        push_cast
        ring
      have htail : tailCorrection n
          = 2 * ((normalizedCoefficient (n / 2) : ℚ) : ℂ) / (n : ℂ) ^ 2 := by
        unfold tailCorrection
        rw [if_pos hd]
      rw [htail, hcast]
      try ring
    · have hq : halfScaleScaled n = normalizedCoefficient n := by
        unfold halfScaleScaled halfScaleRemainder
        rw [if_neg hn0, if_neg hd]
        field_simp
        ring
      have hcast : ((halfScaleScaled n : ℚ) : ℂ) = ((normalizedCoefficient n : ℚ) : ℂ) := by
        rw [hq]
      have htail : tailCorrection n = 0 := by
        unfold tailCorrection
        rw [if_neg hd]
      rw [htail, hcast]
      try ring
  have hres := Tendsto.congr' hEq hdiff
  simpa using hres

set_option maxHeartbeats 600000 in
/-- The normalized coefficients are bounded. -/
theorem halfScaleScaled_bound (h : ExtremalAsymptotic) :
    ∃ C : ℝ, ∀ n, ‖((halfScaleScaled n : ℚ) : ℂ)‖ ≤ C := by
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto _ (halfScaleScaled_tendsto h)).exists_norm_le
  exact ⟨C, fun n => hC _ ⟨n, rfl⟩⟩

set_option maxHeartbeats 600000 in
/-- The remainder coefficients grow at most quadratically. -/
theorem remainder_coeff_bound (h : ExtremalAsymptotic) :
    ∃ C : ℝ, ∀ n, ‖((halfScaleRemainder n : ℚ) : ℂ)‖ ≤ C * (n : ℝ) ^ 2 := by
  obtain ⟨C, hC⟩ := halfScaleScaled_bound h
  refine ⟨C, fun n => ?_⟩
  have hnn : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
  rw [← scaled_mul_sq n, norm_mul, norm_sq_natCast]
  calc (n : ℝ) ^ 2 * ‖((halfScaleScaled n : ℚ) : ℂ)‖
      ≤ (n : ℝ) ^ 2 * C := mul_le_mul_of_nonneg_left (hC n) hnn
    _ = C * (n : ℝ) ^ 2 := by ring

set_option maxHeartbeats 600000 in
/-- The evaluated remainder series is absolutely convergent inside the disc. -/
theorem halfScale_hasSeriesValue (h : ExtremalAsymptotic) :
    ∀ r : ℝ, (0 : ℝ) < r → r < 1 →
      HasSeriesValue halfScaleSeries (r : ℂ) (∑' k, seriesTerm halfScaleSeries (r : ℂ) k) := by
  obtain ⟨C, hC⟩ := remainder_coeff_bound h
  have hCnn : (0 : ℝ) ≤ C := by
    have h1 := hC 1
    have h2 : (0 : ℝ) ≤ C * (((1 : ℕ)) : ℝ) ^ 2 := le_trans (norm_nonneg _) h1
    simpa using h2
  intro r hr0 hr1
  have hrnorm : ‖(r : ℂ)‖ < 1 := by
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0] using hr1
  have hg : Summable fun n : ℕ => C * ‖(n : ℂ) ^ 2 * (r : ℂ) ^ n‖ :=
    (summable_norm_pow_mul_geometric_of_norm_lt_one 2 hrnorm).mul_left C
  have hterm : ∀ n : ℕ, ‖seriesTerm halfScaleSeries (r : ℂ) n‖
      ≤ C * ‖(n : ℂ) ^ 2 * (r : ℂ) ^ n‖ := by
    intro n
    have hb := hC n
    have hval : seriesTerm halfScaleSeries (r : ℂ) n
        = ((halfScaleRemainder n : ℚ) : ℂ) * (r : ℂ) ^ n := by
      simp [seriesTerm, halfScaleSeries]
    rw [hval, norm_mul, norm_mul, norm_sq_natCast]
    have h0 : (0 : ℝ) ≤ ‖(r : ℂ) ^ n‖ := norm_nonneg _
    calc ‖((halfScaleRemainder n : ℚ) : ℂ)‖ * ‖(r : ℂ) ^ n‖
        ≤ (C * (n : ℝ) ^ 2) * ‖(r : ℂ) ^ n‖ := mul_le_mul_of_nonneg_right hb h0
      _ = C * ((n : ℝ) ^ 2 * ‖(r : ℂ) ^ n‖) := by ring
  have hs : Summable fun n : ℕ => ‖seriesTerm halfScaleSeries (r : ℂ) n‖ := by
    refine Summable.of_norm_bounded (hg := hg) (fun n => ?_)
    rw [norm_norm]
    exact hterm n
  exact ⟨hs, hs.of_norm.hasSum⟩

set_option maxHeartbeats 600000 in
/-- The `(1-r)^3`-normalized radial limit of `M` is `2L`. -/
theorem halfScale_radial (h : ExtremalAsymptotic) :
    Tendsto (fun r : ℝ => (1 - (r : ℂ)) ^ 3 * ∑' k, seriesTerm halfScaleSeries (r : ℂ) k)
      (𝓝[<] 1) (𝓝 (2 * extremalConstant)) := by
  have hc := halfScaleScaled_tendsto h
  have hw := abel_sq_weight (fun n => ((halfScaleScaled n : ℚ) : ℂ)) extremalConstant hc
  refine Tendsto.congr' ?_ hw
  filter_upwards with r
  congr 1
  apply tsum_congr
  intro n
  have hval : seriesTerm halfScaleSeries (r : ℂ) n
      = ((halfScaleRemainder n : ℚ) : ℂ) * (r : ℂ) ^ n := by
    simp [seriesTerm, halfScaleSeries]
  rw [hval, ← scaled_mul_sq n]
  simp only [sqterm]
  try ring

/-- Twice a transcendental number is transcendental. -/
theorem transcendental_two_mul {x : ℂ} (h : Transcendental ℚ x) :
    Transcendental ℚ (2 * x) := by
  intro hx
  apply h
  have hcast : ((algebraMap ℚ ℂ) (1 / 2)) = (1 / 2 : ℂ) := by norm_num
  have hhalf : IsAlgebraic ℚ ((1 / 2 : ℂ)) := by
    rw [← hcast]
    exact isAlgebraic_algebraMap (1 / 2)
  have hthis : IsAlgebraic ℚ ((2 * x) * (1 / 2 : ℂ)) := hx.mul hhalf
  have heq : (2 * x) * (1 / 2 : ℂ) = x := by ring
  rwa [heq] at hthis

set_option maxHeartbeats 600000 in
/-- `M` admits no nonzero complex polynomial relation. -/
theorem halfScale_nonalgebraic (h : ExtremalAsymptotic) (lw : FourExponentialIndependence) :
    ¬ HasPolynomialRelation (PowerSeries.map (algebraMap ℚ ℂ) halfScaleSeries) :=
  nonalgebraic_of_radial_limit halfScaleSeries (2 * extremalConstant) 3
    (halfScale_hasSeriesValue h) (halfScale_radial h)
    (transcendental_two_mul (extremalConstant_transcendental lw))

set_option maxHeartbeats 600000 in
/-- Standard mathlib formulation for `M`. -/
theorem halfScale_transcendental (h : ExtremalAsymptotic) (lw : FourExponentialIndependence) :
    Transcendental (Polynomial ℂ)
      (PowerSeries.map (algebraMap ℚ ℂ) halfScaleSeries) := by
  intro hrel
  exact halfScale_nonalgebraic h lw (hasPolynomialRelation_of_isAlgebraic _ hrel)

#print axioms halfScaleScaled_tendsto
#print axioms remainder_coeff_bound
#print axioms halfScale_radial
#print axioms halfScale_nonalgebraic
#print axioms halfScale_transcendental

end NonAlgebraicity
