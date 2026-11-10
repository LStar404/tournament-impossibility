import SummedGammaAbsorptionCandidate
import CoreMinorEnvelopeCandidate
set_option autoImplicit false
noncomputable section
namespace LogWindowGammaAbsorptionCandidate
open Filter
open scoped Topology
open TournamentHamiltonian ActualTournamentPrescalingBounds TournamentPrescalingMassBound
open NonprincipalReconstructionCandidate SummedGammaAbsorptionCandidate

lemma eventually_scalar_gates (A c : ℝ) (hc : 0 ≤ c) :
    ∀ᶠ n : ℕ in atTop, ∀ t : ℝ, 0 ≤ t → t ≤ A*Real.log (n:ℝ) →
      0 < n ∧ c*((1+t)/(n:ℝ)+Real.sqrt (t/(n:ℝ))) ≤ 1/4 ∧ (c^2+c)/(n:ℝ) ≤ 1 := by
  have hr := (CoreMinorEnvelopeCandidate.rEnvelope_tendsto A A).const_mul c
  simp only [mul_zero] at hr
  have hi : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hb := hi.const_mul (c^2+c)
  simp only [mul_zero] at hb
  filter_upwards [eventually_gt_atTop 0, hr.eventually_le_const (by norm_num : (0:ℝ)<1/4),
    hb.eventually_le_const (by norm_num : (0:ℝ)<1)] with n hn hrn hbn
  intro t ht hta
  refine ⟨hn, ?_, ?_⟩
  · apply le_trans _ hrn
    apply mul_le_mul_of_nonneg_left _ hc
    unfold CoreMinorEnvelopeCandidate.rEnvelope
    have hs := Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hta (Nat.cast_nonneg n))
    have hh := div_le_div_of_nonneg_right (add_le_add (le_refl (1:ℝ)) hta) (Nat.cast_nonneg n)
    rw [add_comm 1 (A*Real.log (n:ℝ))] at hh
    linarith
  · simpa only [div_eq_mul_inv] using hbn

theorem eventually_actual_absorption (A c : ℝ) (hc : 0 ≤ c) {a0 : ℝ}
    (h0 : 0 ≤ a0) (h1 : a0 < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ (T : Tournament n) (E : ℝ),
      (∀ i, |normalizedScore T i| ≤ a0) →
      tau (normalizedScore T) ≤ A*Real.log (n:ℝ) →
      E ≤ c*budget (tau (normalizedScore T)) n →
      gamma (normalizedScore T)*Real.exp E ≤
        Real.exp (-tau (normalizedScore T)/2)+Real.exp 1*(c^2+c)/(n:ℝ) := by
  filter_upwards [eventually_scalar_gates A c hc] with n hg
  intro T E ha hτ hE
  obtain ⟨hn, hs, hb⟩ := hg _ (tau_nonneg _) hτ
  exact actual_gamma_summed_additive T hn h0 h1 ha hc hs hE hb
end LogWindowGammaAbsorptionCandidate
