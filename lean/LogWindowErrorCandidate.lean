import ActualNormalizedCenteredGapCandidate
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Uniform log-energy window, no linear-energy or extremality premise. -/
set_option autoImplicit false
noncomputable section
namespace LogWindowErrorCandidate
open Filter Asymptotics
open TournamentHamiltonian ActualTournamentPrescalingBounds ActualPrescalingNormalization
open TournamentPrescalingMassBound ActualNormalizedCenteredGapCandidate
open scoped Topology

lemma log_power_decay (k : ℕ) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun n : ℕ => (Real.log (n:ℝ))^k / (n:ℝ)^r) atTop (𝓝 0) := by
  have hh := (isLittleO_log_rpow_rpow_atTop (k:ℝ) hr).tendsto_div_nhds_zero
  simpa only [Real.rpow_natCast, Function.comp_def] using hh.comp tendsto_natCast_atTop_atTop

lemma log_sqrt_decay (k : ℕ) :
    Tendsto (fun n : ℕ => (Real.log (n:ℝ))^k / Real.sqrt (n:ℝ)) atTop (𝓝 0) := by
  simpa only [Real.sqrt_eq_rpow] using log_power_decay k (by norm_num : (0:ℝ)<1/2)

def massEnvelope (A : ℝ) (n : ℕ) : ℝ :=
  (A*Real.log (n:ℝ)+(A*Real.log (n:ℝ))^2)/(n:ℝ)+
    (A*Real.log (n:ℝ)+(A*Real.log (n:ℝ))^2)/Real.sqrt (n:ℝ)

lemma massEnvelope_tendsto (A : ℝ) : Tendsto (massEnvelope A) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => Real.log (n:ℝ)/(n:ℝ)) atTop (𝓝 0) := by
    simpa using log_power_decay 1 (by norm_num : (0:ℝ)<1)
  have h2 : Tendsto (fun n : ℕ => Real.log (n:ℝ)^2/(n:ℝ)) atTop (𝓝 0) := by
    simpa using log_power_decay 2 (by norm_num : (0:ℝ)<1)
  have h3 := log_sqrt_decay 1
  have h4 := log_sqrt_decay 2
  have hh := ((h1.const_mul A).add (h2.const_mul (A^2))).add
    ((h3.const_mul A).add (h4.const_mul (A^2)))
  convert hh using 1
  · funext n
    unfold massEnvelope
    simp only [pow_one]
    ring
  · simp

lemma sqrt_le_add_one {t : ℝ} (ht : 0 ≤ t) : Real.sqrt t ≤ t+1 := by
  have hs := Real.sq_sqrt ht
  have hn := Real.sqrt_nonneg t
  nlinarith [sq_nonneg (Real.sqrt t-1)]

lemma errorScale_le_envelope {n : ℕ} {t A : ℝ}
    (ht : 0 ≤ t) (hb : t ≤ A*Real.log (n:ℝ)) :
    errorScale n t ≤ massEnvelope A n := by
  have hu : 0 ≤ A*Real.log (n:ℝ) := ht.trans hb
  have hs := sqrt_le_add_one ht
  have hnum : t*Real.sqrt t ≤ A*Real.log (n:ℝ)+(A*Real.log (n:ℝ))^2 := by
    have hmul := mul_le_mul_of_nonneg_left hs ht
    have hsq : t^2 ≤ (A*Real.log (n:ℝ))^2 := pow_le_pow_left₀ ht hb 2
    nlinarith
  unfold errorScale massEnvelope
  apply add_le_add
  · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    nlinarith [pow_le_pow_left₀ ht hb 2]
  · exact div_le_div_of_nonneg_right hnum (Real.sqrt_nonneg _)

def actualMassEnvelope (A a0 : ℝ) (n : ℕ) : ℝ :=
  4*(radiusFactor a0)^2*massEnvelope A n

def energyEnvelope (A a0 : ℝ) (n : ℕ) : ℝ :=
  128*(scaleCap a0)^4*(A*Real.log (n:ℝ))/(n:ℝ)+
    512*(scaleCap a0)^4*(actualMassEnvelope A a0 n)^2/(n:ℝ)^2

lemma actual_mass_le {n : ℕ} (T : Tournament n) {A a0 : ℝ}
    (ht : tau (normalizedScore T) ≤ A*Real.log (n:ℝ)) :
    massBound T a0 ≤ actualMassEnvelope A a0 n := by
  exact mul_le_mul_of_nonneg_left (errorScale_le_envelope (tau_nonneg _) ht) (by positivity)

lemma actual_energy_le {n : ℕ} (T : Tournament n) {A a0 : ℝ}
    (ht : tau (normalizedScore T) ≤ A*Real.log (n:ℝ)) :
    errorBudget T a0 ≤ energyEnvelope A a0 n := by
  have hm := actual_mass_le T (a0:=a0) ht
  have hp := massBound_nonneg T a0
  unfold errorBudget energyEnvelope
  apply add_le_add
  · gcongr
  · have hsq := pow_le_pow_left₀ hp hm 2
    gcongr

lemma energyEnvelope_tendsto (A a0 : ℝ) :
    Tendsto (energyEnvelope A a0) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n:ℝ)/(n:ℝ)) atTop (𝓝 0) := by
    simpa using log_power_decay 1 (by norm_num : (0:ℝ)<1)
  have hmass : Tendsto (actualMassEnvelope A a0) atTop (𝓝 0) := by
    change Tendsto (fun n => 4*(radiusFactor a0)^2*massEnvelope A n) atTop (𝓝 0)
    simpa only [mul_zero] using (massEnvelope_tendsto A).const_mul (4*(radiusFactor a0)^2)
  have hinv : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hh := (hlog.const_mul (128*(scaleCap a0)^4*A)).add
    (((hmass.pow 2).mul (hinv.pow 2)).const_mul (512*(scaleCap a0)^4))
  convert hh using 1
  · funext n
    unfold energyEnvelope
    simp only [div_eq_mul_inv, inv_pow]
    ring
  · simp

/-- One N works for every actual tournament in the log-energy window. -/
theorem eventually_actual_error_small (A a0 : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ T : Tournament n,
      tau (normalizedScore T) ≤ A*Real.log (n:ℝ) →
      Real.sqrt (errorBudget T a0) ≤ 1/46 := by
  have hh : Tendsto (fun n => Real.sqrt (energyEnvelope A a0 n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp (energyEnvelope_tendsto A a0)
  filter_upwards [hh.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/46))] with n hn
  intro T ht
  exact (Real.sqrt_le_sqrt (actual_energy_le T ht)).trans hn.le
end LogWindowErrorCandidate
