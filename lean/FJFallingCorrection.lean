import FJRadialTail
import Mathlib

/-! Shared candidate, validated locally; repository integration is separate.
The n^-2 correction is proved before using any analytic derivative. -/
noncomputable section
open Filter Topology Finset
namespace FJFallingCorrection

theorem ratio_le_one (k : ℕ) {n : ℕ} (hn : 0<n) :
    (n.descFactorial k : ℝ)/(n : ℝ)^k ≤ 1 := by
  apply (div_le_one (by positivity : 0<(n : ℝ)^k)).mpr
  exact_mod_cast Nat.descFactorial_le_pow n k

/-- An elementary induction, rather than an unspecified polynomial O bound. -/
theorem defect_bound_of_le (k : ℕ) {n : ℕ} (hn : 0<n) (hk : k≤n) :
    1-(n.descFactorial k : ℝ)/(n : ℝ)^k ≤ (k : ℝ)^2/(n : ℝ) := by
  revert hk
  induction k with
  | zero => intro hk; simp
  | succ k ih =>
    intro hk
    have hkn : k≤n := by omega
    have hI := ih hkn
    have hn0 : (0 : ℝ)<n := by exact_mod_cast hn
    have hnne : (n : ℝ)≠0 := ne_of_gt hn0
    have hA := ratio_le_one k hn
    have he : 1-(n.descFactorial (k+1) : ℝ)/(n : ℝ)^(k+1) =
        (1-(n.descFactorial k : ℝ)/(n : ℝ)^k) +
          ((k : ℝ)/(n : ℝ))*((n.descFactorial k : ℝ)/(n : ℝ)^k) := by
      rw [Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_sub hkn, pow_succ]
      field_simp [hnne]
      ring
    rw [he]
    have hm := mul_le_mul_of_nonneg_left hA
      (by positivity : 0≤(k : ℝ)/(n : ℝ))
    calc
      _ ≤ (k : ℝ)^2/(n : ℝ)+(k : ℝ)/(n : ℝ) := by linarith
      _ ≤ ((k+1 : ℕ) : ℝ)^2/(n : ℝ) := by
        rw [← add_div]
        apply div_le_div_of_nonneg_right _ hn0.le
        push_cast
        nlinarith [show (0 : ℝ)≤k by positivity]

/-- Uniform in every n≥1, including the n<k range where the factorial is zero. -/
theorem correction_bound_real (k : ℕ) {n : ℕ} (hn : 0<n) :
    |(n.descFactorial k : ℝ)/(n : ℝ)^(k+1)-1/(n : ℝ)|
      ≤ ((k+1 : ℕ) : ℝ)^2/(n : ℝ)^2 := by
  have hn0 : (0 : ℝ)<n := by exact_mod_cast hn
  have hnne : (n : ℝ)≠0 := ne_of_gt hn0
  by_cases hk : k≤n
  · have hd : 0≤1-(n.descFactorial k : ℝ)/(n : ℝ)^k :=
      sub_nonneg.mpr (ratio_le_one k hn)
    have he : (n.descFactorial k : ℝ)/(n : ℝ)^(k+1)-1/(n : ℝ) =
        -(1-(n.descFactorial k : ℝ)/(n : ℝ)^k)/(n : ℝ) := by
      rw [pow_succ]
      field_simp [hnne]
      ring
    rw [he, abs_div, abs_neg, abs_of_nonneg hd, abs_of_pos hn0]
    calc
      _ ≤ ((k : ℝ)^2/(n : ℝ))/(n : ℝ) :=
        div_le_div_of_nonneg_right (defect_bound_of_le k hn hk) hn0.le
      _ = (k : ℝ)^2/(n : ℝ)^2 := by ring
      _ ≤ ((k+1 : ℕ) : ℝ)^2/(n : ℝ)^2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        push_cast
        nlinarith [show (0 : ℝ)≤k by positivity]
  · have hnlt : n<k := by omega
    rw [Nat.descFactorial_of_lt hnlt]
    simp only [Nat.cast_zero, zero_div, zero_sub, abs_neg, abs_div, abs_one,
      abs_of_pos hn0]
    apply (div_le_div_iff₀ hn0 (pow_pos hn0 2)).mpr
    have hnk : (n : ℝ)<k := by exact_mod_cast hnlt
    have hk0 : (0 : ℝ)≤k := by positivity
    have hnk2 : (n : ℝ)≤((k+1 : ℕ) : ℝ)^2 := by
      push_cast
      nlinarith
    have hm := mul_le_mul_of_nonneg_right hnk2 hn0.le
    nlinarith

theorem correction_bound (k : ℕ) {n : ℕ} (hn : 0<n) :
    ‖(n.descFactorial k : ℂ)/(n : ℂ)^(k+1)-1/(n : ℂ)‖
      ≤ ((k+1 : ℕ) : ℝ)^2/(n : ℝ)^2 := by
  have he : (n.descFactorial k : ℂ)/(n : ℂ)^(k+1)-1/(n : ℂ) =
      (((n.descFactorial k : ℝ)/(n : ℝ)^(k+1)-1/(n : ℝ) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [he, Complex.norm_real, Real.norm_eq_abs]
  exact correction_bound_real k hn

/-- Exact conversion of the derivative series to ordinary powers.
The zero falling factorial handles n<h without using negative natural powers. -/
theorem weighted_jet_identity (c : ℕ→ℂ) (h : ℕ) (z : ℂ) :
    (∑' n, c n*(n.descFactorial h : ℂ)*z^n) = z^h*FJRadialTail.jet c h z := by
  unfold FJRadialTail.jet
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  by_cases hn : h≤n
  · unfold FJRadialTail.term
    have hp : z^n = z^(n-h)*z^h := by
      rw [← pow_add, Nat.sub_add_cancel hn]
    rw [hp]
    ring
  · simp [FJRadialTail.term, Nat.descFactorial_of_lt (show n<h by omega)]

/-- The elementary integrable logarithm limit along δ=1-x. -/
theorem delta_log_tendsto :
    Tendsto (fun x : ℝ => (1-x)*Real.log (1-x)) (𝓝[<] 1) (𝓝 0) := by
  have hd : Tendsto (fun x : ℝ => 1-x) (𝓝[<] 1) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (show Tendsto (fun x : ℝ => x) (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℝ)) from tendsto_id.mono_left nhdsWithin_le_nhds)
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact sub_pos.mpr (show x < 1 from hx)
  have h := (tendsto_log_mul_rpow_nhdsGT_zero (by norm_num : (0 : ℝ)<1)).comp hd
  simpa only [Function.comp_def, Real.rpow_one, mul_comm] using h

/-- The apparent x^-k multiplier contributes no extra logarithmic amplitude. -/
theorem inverse_power_log_tendsto_real (k : ℕ) :
    Tendsto (fun x : ℝ => (1/x^k-1)*Real.log (1-x)) (𝓝[<] 1) (𝓝 0) := by
  have hg : ContinuousAt (fun x : ℝ => (∑ i ∈ range k, x^i)/x^k) 1 := by
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · simp
  have ht := delta_log_tendsto.mul (hg.tendsto.mono_left nhdsWithin_le_nhds)
  simp only [zero_mul] at ht
  apply ht.congr'
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ)<1 by norm_num)] with x hx
  have he := mul_neg_geom_sum x k
  have hxne : x≠0 := ne_of_gt hx.1
  field_simp [hxne]
  linear_combination Real.log (1-x)*he

theorem inverse_power_log_tendsto (k : ℕ) :
    Tendsto (fun x : ℝ => (1/(x : ℂ)^k-1)*(Real.log (1-x) : ℂ))
      (𝓝[<] 1) (𝓝 0) := by
  have h := (Complex.continuous_ofReal.tendsto 0).comp (inverse_power_log_tendsto_real k)
  simpa only [Function.comp_def, Complex.ofReal_zero, Complex.ofReal_mul,
    Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_pow] using h

end FJFallingCorrection
#print axioms FJFallingCorrection.correction_bound
#print axioms FJFallingCorrection.weighted_jet_identity
#print axioms FJFallingCorrection.inverse_power_log_tendsto
