import Mathlib

/-!
Standalone abstract backend component. Final evidence: focused/result.json.
No repository source or entry point is changed.
The purpose is the genuinely analytic part needed for the coefficient error:
bounded coefficients => actual interior real radial derivatives;
summable falling-factorial moments => finite endpoint derivative limits.
No boundary analytic continuation or radius > 1 is assumed.
-/
noncomputable section
open Filter Topology
namespace FJRadialTail

def term (c : ℕ → ℂ) (h n : ℕ) (z : ℂ) : ℂ :=
  c n * (n.descFactorial h : ℂ) * z^(n-h)

def jet (c : ℕ → ℂ) (h : ℕ) (z : ℂ) : ℂ := ∑' n, term c h n z

def radial (c : ℕ → ℂ) (x : ℝ) : ℂ := jet c 0 (x : ℂ)

theorem term_derivative (c : ℕ → ℂ) (h n : ℕ) (z : ℂ) :
    HasDerivAt (term c h n) (term c (h+1) n z) z := by
  unfold term
  convert (hasDerivAt_pow (n-h) z).const_mul
    (c n * (n.descFactorial h : ℂ)) using 1
  simp only [Nat.descFactorial_succ, Nat.cast_mul,
    show n-(h+1)=n-h-1 by omega]
  ring

/-- This bound works for 0<R<1. The old >1-radius module has a different
majorant and must not be applied to a singular unit-circle boundary point. -/
theorem term_bound {c : ℕ → ℂ} {C R : ℝ} (hC : 0 ≤ C)
    (hc : ∀ n, ‖c n‖ ≤ C) (hR : 0 < R) (h n : ℕ) {z : ℂ}
    (hz : ‖z‖ ≤ R) :
    ‖term c h n z‖ ≤ (C / R^h) * ((n : ℝ)^h * R^n) := by
  by_cases hn : h ≤ n
  · have hd : (n.descFactorial h : ℝ) ≤ (n : ℝ)^h := by
      exact_mod_cast Nat.descFactorial_le_pow n h
    unfold term
    rw [norm_mul, norm_mul, Complex.norm_natCast, norm_pow]
    calc
      ‖c n‖ * (n.descFactorial h : ℝ) * ‖z‖^(n-h)
          ≤ C * (n : ℝ)^h * R^(n-h) := by
            gcongr
            exact hc n
      _ = (C / R^h) * ((n : ℝ)^h * R^n) := by
        rw [pow_sub₀ R (ne_of_gt hR) hn]
        ring
  · have hz' : n.descFactorial h = 0 := Nat.descFactorial_of_lt (by omega)
    simp only [term, hz', Nat.cast_zero, mul_zero, zero_mul, norm_zero]
    positivity

theorem majorant_summable {C R : ℝ} (hR : 0 < R) (hR1 : R < 1) (h : ℕ) :
    Summable (fun n : ℕ => (C/R^h) * ((n : ℝ)^h * R^n)) := by
  exact (summable_pow_mul_geometric_of_norm_lt_one h
    (by simpa [Real.norm_eq_abs, abs_of_pos hR] using hR1)).mul_left (C/R^h)

theorem term_summable {c : ℕ → ℂ} {C R : ℝ} (hC : 0 ≤ C)
    (hc : ∀ n, ‖c n‖ ≤ C) (hR : 0 < R) (hR1 : R < 1) (h : ℕ)
    {z : ℂ} (hz : ‖z‖ ≤ R) : Summable (fun n => term c h n z) := by
  exact (majorant_summable (C := C) hR hR1 h).of_norm_bounded
    (fun n => term_bound hC hc hR h n hz)

theorem derivative_sum_on_ball {c : ℕ → ℂ} {C R : ℝ} (hC : 0 ≤ C)
    (hc : ∀ n, ‖c n‖ ≤ C) (hR : 0 < R) (hR1 : R < 1) (h : ℕ)
    {z : ℂ} (hz : z ∈ Metric.ball 0 R) :
    HasDerivAt (jet c h) (jet c (h+1) z) z := by
  change HasDerivAt (fun y => ∑' n, term c h n y)
    (∑' n, term c (h+1) n z) z
  apply hasDerivAt_tsum_of_isPreconnected
    (t := Metric.ball (0 : ℂ) R) (y₀ := (0 : ℂ))
    (majorant_summable (C := C) hR hR1 (h+1))
    Metric.isOpen_ball Metric.isPreconnected_ball
  · intro n y _
    exact term_derivative c h n y
  · intro n y hy
    apply term_bound hC hc hR (h+1) n
    exact (by simpa only [Metric.mem_ball, dist_zero_right] using hy : ‖y‖ < R).le
  · simpa only [Metric.mem_ball, dist_self] using hR
  · exact term_summable hC hc hR hR1 h (by simpa using hR.le)
  · exact hz

theorem derivative_sum_inside {c : ℕ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ n, ‖c n‖ ≤ C) (h : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (jet c h) (jet c (h+1) z) z := by
  apply derivative_sum_on_ball hC hc (R := (‖z‖+1)/2)
  · linarith [norm_nonneg z]
  · linarith
  · simp only [Metric.mem_ball, dist_zero_right]
    linarith

/-- Real differentiation of the composed radial function. c already includes
ω^n, so there is no unexplained external factor ω^h. -/
theorem iterated_radial {c : ℕ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ n, ‖c n‖ ≤ C) (h : ℕ) :
    ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      iteratedDeriv h (radial c) x = jet c h (x : ℂ) := by
  induction h with
  | zero => intro x hx; rfl
  | succ h ih =>
    intro x hx
    have he : iteratedDeriv h (radial c) =ᶠ[𝓝 x]
        (fun y : ℝ => jet c h (y : ℂ)) := by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
      exact ih y hy
    rw [iteratedDeriv_succ, he.deriv_eq]
    exact (derivative_sum_inside hC hc h
      (by simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx.1] using hx.2)
      |>.comp_ofReal).deriv

/-- Continuity of the exact derivative series, without a radius >1 claim. -/
theorem jet_continuousOn {c : ℕ → ℂ} (h : ℕ)
    (hs : Summable (fun n => ‖c n‖ * (n.descFactorial h : ℝ))) :
    ContinuousOn (fun x : ℝ => jet c h (x : ℂ)) (Set.Icc 0 1) := by
  apply continuousOn_tsum (u := fun n => ‖c n‖ * (n.descFactorial h : ℝ))
  · intro n
    unfold term
    fun_prop
  · exact hs
  · intro n x hx
    have hxnorm : ‖(x : ℂ)‖ ≤ 1 := by
      simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2
    unfold term
    rw [norm_mul, norm_mul, Complex.norm_natCast, norm_pow]
    exact mul_le_of_le_one_right (by positivity)
      (pow_le_one₀ (norm_nonneg _) hxnorm)

theorem jet_tendsto {c : ℕ → ℂ} (h : ℕ)
    (hs : Summable (fun n => ‖c n‖ * (n.descFactorial h : ℝ))) :
    Tendsto (fun x : ℝ => jet c h (x : ℂ)) (𝓝[<] 1)
      (𝓝 (∑' n, c n * (n.descFactorial h : ℂ))) := by
  have hid : Tendsto (fun x : ℝ => x) (𝓝[<] 1) (𝓝[Set.Icc 0 1] 1) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_id.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with x hx
    exact ⟨hx.1.le, hx.2.le⟩
  have ht := (jet_continuousOn h hs 1 (by simp)).tendsto.comp hid
  simpa only [Function.comp_def, Complex.ofReal_one, jet, term, one_pow, mul_one] using ht

/-- This is an actual iterated-derivative limit, not a coefficient-series
renaming: iterated_radial has supplied the interior identification. -/
theorem iterated_radial_tendsto {c : ℕ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ n, ‖c n‖ ≤ C) (h : ℕ)
    (hs : Summable (fun n => ‖c n‖ * (n.descFactorial h : ℝ))) :
    Tendsto (iteratedDeriv h (radial c)) (𝓝[<] 1)
      (𝓝 (∑' n, c n * (n.descFactorial h : ℂ))) := by
  apply (jet_tendsto h hs).congr'
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with x hx
  exact (iterated_radial hC hc h x hx).symm

/-- The needed n^-2 majorant comes from coefficient decay, before any
function is differentiated. This also covers all lower derivative orders. -/
theorem falling_moment_bound {k h n : ℕ} (hh : h ≤ k) (hn : 0 < n)
    {C : ℝ} (hC : 0 ≤ C) {v : ℂ} (hv : ‖v‖ ≤ C / (n : ℝ)^(k+2)) :
    ‖v‖ * (n.descFactorial h : ℝ) ≤ C / (n : ℝ)^2 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hd : (n.descFactorial h : ℝ) ≤ (n : ℝ)^h := by
    exact_mod_cast Nat.descFactorial_le_pow n h
  calc
    ‖v‖ * (n.descFactorial h : ℝ)
        ≤ (C / (n : ℝ)^(k+2)) * (n : ℝ)^h := by gcongr
    _ ≤ (C / (n : ℝ)^(k+2)) * (n : ℝ)^k := by gcongr
    _ = C / (n : ℝ)^2 := by
      rw [pow_add]
      field_simp [hn0]

/-- A global positive-index decay bound gives all the required moments.
A merely eventual bound is reduced to this one by increasing C, since the
prefix is finite. The value c 0 is harmless and need not vanish. -/
theorem falling_moment_summable {c : ℕ → ℂ} {k : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ n : ℕ, 0 < n → ‖c n‖ ≤ C / (n : ℝ)^(k+2))
    {h : ℕ} (hh : h ≤ k) :
    Summable (fun n => ‖c n‖ * (n.descFactorial h : ℝ)) := by
  have hp : Summable (fun n : ℕ => 1 / (n : ℝ)^2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hps : Summable (fun n : ℕ => C / ((n+1 : ℕ) : ℝ)^2) := by
    simpa only [mul_one_div] using ((summable_nat_add_iff 1).mpr hp).mul_left C
  apply (summable_nat_add_iff 1).mp
  exact hps.of_nonneg_of_le (fun n => by positivity)
    (fun n => falling_moment_bound hh (by omega) hC (hc (n+1) (by omega)))

#print axioms FJRadialTail.iterated_radial
#print axioms FJRadialTail.iterated_radial_tendsto
#print axioms FJRadialTail.falling_moment_summable
end FJRadialTail
