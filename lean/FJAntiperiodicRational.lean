import Mathlib

/-!
Standalone abstract backend component; final evidence: focused/result.json.
Only coefficient antiperiodicity is assumed. Boundedness, an exact rational
identity, the analytic extension, and limits of actual radial derivatives
are proved below. No radial limit or log conclusion is an input.
-/
noncomputable section
open Filter Topology Finset
namespace FJAntiperiodicRational

def series (v : ℕ → ℂ) (z : ℂ) : ℂ := ∑' n, v n * z^n

def block (v : ℕ → ℂ) (b : ℕ) (z : ℂ) : ℂ :=
  ∑ n ∈ range b, v n * z^n

def rationalExtension (v : ℕ → ℂ) (b : ℕ) (z : ℂ) : ℂ :=
  block v b z / (1+z^b)

/-- A finite, explicit norm bound, derived from antiperiodicity. -/
theorem antiperiodic_bound {v : ℕ → ℂ} {b : ℕ} (hb : 0 < b)
    (hv : Function.Antiperiodic v b) :
    ∀ n, ‖v n‖ ≤ ∑ t ∈ range b, ‖v t‖ := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < b
    · exact Finset.single_le_sum (fun t _ => norm_nonneg (v t))
        (Finset.mem_range.mpr hn)
    · have hbn : b ≤ n := by omega
      have he : ‖v n‖ = ‖v (n-b)‖ := by
        have hh := hv (n-b)
        rw [Nat.sub_add_cancel hbn] at hh
        rw [hh, norm_neg]
      rw [he]
      exact ih (n-b) (by omega)

theorem summable_series {v : ℕ → ℂ} {b : ℕ} (hb : 0 < b)
    (hv : Function.Antiperiodic v b) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n => v n * z^n) := by
  apply ((summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left
    (∑ t ∈ range b, ‖v t‖)).of_norm_bounded
  intro n
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_right (antiperiodic_bound hb hv n)
    (pow_nonneg (norm_nonneg z) n)

/-- The exact block identity; no limiting or differentiating big-O terms. -/
theorem series_identity {v : ℕ → ℂ} {b : ℕ} (hb : 0 < b)
    (hv : Function.Antiperiodic v b) {z : ℂ} (hz : ‖z‖ < 1) :
    (1+z^b) * series v z = block v b z := by
  have hs := summable_series hb hv hz
  have hsplit := hs.sum_add_tsum_nat_add b
  have htail : (∑' n, v (n+b)*z^(n+b)) = -(z^b)*series v z := by
    calc
      (∑' n, v (n+b)*z^(n+b)) = ∑' n, (-(z^b))*(v n*z^n) := by
        apply tsum_congr
        intro n
        rw [hv n, pow_add]
        ring
      _ = -(z^b)*series v z := by rw [tsum_mul_left]; rfl
  rw [htail] at hsplit
  change block v b z + -(z^b)*series v z = series v z at hsplit
  linear_combination -hsplit

theorem denominator_ne_zero {b : ℕ} (hb : 0 < b) {z : ℂ} (hz : ‖z‖ < 1) :
    1+z^b ≠ 0 := by
  intro h
  have hp : z^b = -1 := by linear_combination h
  have hn := congrArg norm hp
  simp only [norm_pow, norm_neg, norm_one] at hn
  have hlt : ‖z‖^b < 1 := pow_lt_one₀ (norm_nonneg z) hz (by omega)
  linarith

/-- Equality with a fixed rational function throughout the open disk. -/
theorem series_eq_rational {v : ℕ → ℂ} {b : ℕ} (hb : 0 < b)
    (hv : Function.Antiperiodic v b) {z : ℂ} (hz : ‖z‖ < 1) :
    series v z = rationalExtension v b z := by
  unfold rationalExtension
  apply (eq_div_iff (denominator_ne_zero hb hz)).mpr
  simpa only [mul_comm] using series_identity hb hv hz

/-- Analyticity belongs to the explicit rational extension, not to a claim
that the unconditionally interpreted tsum converges at or outside 1. -/
theorem rational_analyticAt_one (v : ℕ → ℂ) (b : ℕ) :
    AnalyticAt ℂ (rationalExtension v b) 1 := by
  have hn : AnalyticAt ℂ (block v b) 1 := by
    unfold block
    exact Finset.analyticAt_fun_sum _
      (fun n _ => analyticAt_const.mul (analyticAt_id.pow n))
  have hd : AnalyticAt ℂ (fun z : ℂ => 1+z^b) 1 :=
    analyticAt_const.add (analyticAt_id.pow b)
  exact hn.div hd (by norm_num)

/-- Every actual real radial derivative has a finite left-hand endpoint
limit for the unweighted antiperiodic series. The value at x=1 is taken from
the rational extension, not from the original tsum function at the boundary. -/
theorem radial_derivatives_tendsto {v : ℕ → ℂ} {b : ℕ} (hb : 0 < b)
    (hv : Function.Antiperiodic v b) (h : ℕ) :
    Tendsto (iteratedDeriv h (fun x : ℝ => series v (x : ℂ))) (𝓝[<] 1)
      (𝓝 (iteratedDeriv h (fun x : ℝ => rationalExtension v b (x : ℂ)) 1)) := by
  have hgC : AnalyticAt ℝ (rationalExtension v b) (1 : ℂ) :=
    (rational_analyticAt_one v b).restrictScalars
  have hg : AnalyticAt ℝ (fun x : ℝ => rationalExtension v b (x : ℂ)) 1 := by
    exact AnalyticAt.comp (f := fun x : ℝ => (x : ℂ)) (x := 1)
      (by simpa using hgC) (Complex.ofRealCLM.analyticAt 1)
  have hcont : ContinuousAt
      (iteratedDeriv h (fun x : ℝ => rationalExtension v b (x : ℂ))) 1 := by
    rw [iteratedDeriv_eq_iterate]
    exact (hg.iterated_deriv h).continuousAt
  apply (hcont.tendsto.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ)<1 by norm_num)] with x hx
  have he : (fun y : ℝ => series v (y : ℂ)) =ᶠ[𝓝 x]
      (fun y : ℝ => rationalExtension v b (y : ℂ)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact series_eq_rational hb hv
      (by simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy.1] using hy.2)
  exact (Filter.EventuallyEq.iteratedDeriv_eq h he).symm

#print axioms FJAntiperiodicRational.antiperiodic_bound
#print axioms FJAntiperiodicRational.series_eq_rational
#print axioms FJAntiperiodicRational.rational_analyticAt_one
#print axioms FJAntiperiodicRational.radial_derivatives_tendsto
end FJAntiperiodicRational
