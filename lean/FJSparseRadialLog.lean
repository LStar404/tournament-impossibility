import FJFallingCorrection
import FJSparseHarmonic
import FJRadialTail

/-! Shared candidate; see focused/runs/final62/result.json for validation. A genuine k-th real radial logarithm theorem for the sparse
jump, derived from coefficients. No function-level O term is differentiated. -/
noncomputable section
open Filter Topology
namespace FJSparseRadialLog
open FJFallingCorrection

def coefficient (q d n : ℕ) : ℂ := if q ∣ n then 1/(n : ℂ)^d else 0

def correction (q k n : ℕ) : ℂ :=
  if q ∣ n then (n.descFactorial k : ℂ)/(n : ℂ)^(k+1)-1/(n : ℂ) else 0

theorem coefficient_bound (q d : ℕ) {n : ℕ} (hn : 0<n) :
    ‖coefficient q d n‖ ≤ 1/(n : ℝ)^d := by
  by_cases h : q∣n
  · simp [coefficient, h, norm_div, norm_pow, Complex.norm_natCast]
  · simp only [coefficient, if_neg h, norm_zero]
    positivity

theorem coefficient_bounded (q d : ℕ) (hd : 0<d) :
    ∀ n, ‖coefficient q d n‖ ≤ 1 := by
  intro n
  by_cases hn : n=0
  · simp [coefficient, hn, zero_pow (by omega : d≠0)]
  · have hnpos : 0<n := by omega
    have hn1 : (1 : ℝ)≤n := by exact_mod_cast hnpos
    have hp : (1 : ℝ)≤(n : ℝ)^d := one_le_pow₀ hn1
    exact (coefficient_bound q d hnpos).trans
      ((div_le_one (by positivity : (0 : ℝ)<(n : ℝ)^d)).mpr hp)

theorem correction_decay (q k : ℕ) {n : ℕ} (hn : 0<n) :
    ‖correction q k n‖ ≤ ((k+1 : ℕ) : ℝ)^2/(n : ℝ)^2 := by
  by_cases h : q∣n
  · simpa only [correction, if_pos h] using correction_bound k hn
  · simp only [correction, if_neg h, norm_zero]
    positivity

theorem correction_norm_summable (q k : ℕ) :
    Summable (fun n => ‖correction q k n‖) := by
  have h := FJRadialTail.falling_moment_summable (c := correction q k) (k := 0)
    (C := ((k+1 : ℕ) : ℝ)^2) (by positivity)
    (fun n hn => by simpa using correction_decay q k hn) (h := 0) (by omega)
  simpa using h

theorem correction_series_summable (q k : ℕ) {z : ℂ} (hz : ‖z‖≤1) :
    Summable (fun n => correction q k n*z^n) := by
  apply (correction_norm_summable q k).of_norm_bounded
  intro n
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg z) hz)

theorem lower_radial_tendsto (q k h : ℕ) (hh : h<k) :
    Tendsto (iteratedDeriv h (FJRadialTail.radial (coefficient q (k+1)))) (𝓝[<] 1)
      (𝓝 (∑' n, coefficient q (k+1) n*(n.descFactorial h : ℂ))) := by
  have hd : ∀ n : ℕ, 0<n →
      ‖coefficient q (k+1) n‖ ≤ 1/(n : ℝ)^((k-1)+2) := by
    intro n hn
    simpa only [show (k-1)+2=k+1 by omega] using coefficient_bound q (k+1) hn
  exact FJRadialTail.iterated_radial_tendsto (by norm_num)
    (coefficient_bounded q (k+1) (by omega)) h
    (FJRadialTail.falling_moment_summable (by norm_num) hd (by omega : h≤k-1))

/-- Exact weighted identity for the actual highest derivative. -/
theorem highest_identity (q : ℕ) (hq : 0<q) (k : ℕ) {x : ℝ}
    (hx : x∈Set.Ioo 0 1) :
    (x : ℂ)^k*iteratedDeriv k (FJRadialTail.radial (coefficient q (k+1))) x =
      FJSparseHarmonic.sparseHarmonic q (x : ℂ) +
        ∑' n, correction q k n*(x : ℂ)^n := by
  have hxn : ‖(x : ℂ)‖<1 := by
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx.1] using hx.2
  rw [FJRadialTail.iterated_radial (by norm_num)
    (coefficient_bounded q (k+1) (by omega)) k x hx, ← weighted_jet_identity]
  have hsH := (FJSparseHarmonic.hasSum_sparse_harmonic q hq hxn).summable
  have hsB := correction_series_summable q k hxn.le
  calc
    _ = ∑' n, (FJSparseHarmonic.sparseTerm q (x : ℂ) n +
        correction q k n*(x : ℂ)^n) := by
      apply tsum_congr
      intro n
      by_cases h : q∣n
      · simp only [coefficient, correction, FJSparseHarmonic.sparseTerm, if_pos h]
        ring
      · simp [coefficient, correction, FJSparseHarmonic.sparseTerm, h]
    _ = _ := hsH.tsum_add hsB

/-- The sparse jump has a genuine k-th derivative logarithm. The constant
includes a convergent correction series and the exact -log(q)/q term. -/
theorem highest_radial_log_tendsto (q : ℕ) (hq : 0<q) (k : ℕ) :
    Tendsto (fun x : ℝ =>
      iteratedDeriv k (FJRadialTail.radial (coefficient q (k+1))) x +
        (Real.log (1-x) : ℂ)/(q : ℂ)) (𝓝[<] 1)
      (𝓝 (-(Real.log (q : ℝ) : ℂ)/(q : ℂ)+∑' n, correction q k n)) := by
  have hx : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[<] 1) (𝓝 (1 : ℂ)) :=
    Complex.continuous_ofReal.tendsto (1 : ℝ) |>.mono_left nhdsWithin_le_nhds
  have hI : Tendsto (fun x : ℝ => 1/(x : ℂ)^k) (𝓝[<] 1) (𝓝 (1 : ℂ)) := by
    simpa only [one_div, one_pow, inv_one] using (hx.pow k).inv₀ (by simp : (1 : ℂ)^k≠0)
  have hB : Tendsto (fun x : ℝ => ∑' n, correction q k n*(x : ℂ)^n)
      (𝓝[<] 1) (𝓝 (∑' n, correction q k n)) := by
    simpa [FJRadialTail.jet, FJRadialTail.term] using
      FJRadialTail.jet_tendsto (c := correction q k) 0
        (by simpa using correction_norm_summable q k)
  have hH := FJSparseHarmonic.sparse_harmonic_regular_part_tendsto q hq
  have hsmall := (inverse_power_log_tendsto k).div_const (q : ℂ)
  have ht := (hI.mul (hH.add hB)).sub hsmall
  simp only [one_mul, zero_div, sub_zero] at ht
  apply ht.congr'
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ)<1 by norm_num)] with x hxi
  have hid := highest_identity q hq k hxi
  have hxn : (x : ℂ)≠0 := by exact_mod_cast (ne_of_gt hxi.1)
  have he : iteratedDeriv k (FJRadialTail.radial (coefficient q (k+1))) x =
      (FJSparseHarmonic.sparseHarmonic q (x : ℂ)+
        ∑' n, correction q k n*(x : ℂ)^n)/(x : ℂ)^k := by
    apply (eq_div_iff (pow_ne_zero k hxn)).mpr
    simpa only [mul_comm] using hid
  rw [he]
  ring

end FJSparseRadialLog
#print axioms FJSparseRadialLog.correction_norm_summable
#print axioms FJSparseRadialLog.lower_radial_tendsto
#print axioms FJSparseRadialLog.highest_radial_log_tendsto
