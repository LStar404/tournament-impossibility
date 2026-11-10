import ActualSharpSpectralCandidate
import ActualCoarseUpperClosureCandidate
import ActualMaximizerEnergyCandidate

/-! Isolated sharp path and actual-maximizer energy closure.
This does not assert classification, actual F/J, or R. -/
set_option autoImplicit false
noncomputable section
namespace ActualSharpPathEnergyCandidate
open TournamentHamiltonian ActualTournamentPrescalingBounds TournamentPrescalingMassBound
open Filter
open scoped Topology

theorem actual_maxPaths_upper_uniform :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      (maxPaths n : ℝ) / meanPaths n ≤ lowerConstant + C / (n : ℝ) := by
  obtain ⟨Cp, hCp, hpath⟩ := ActualCappedPathUpperCandidate.actual_capped_path_upper_weak
    (256 : ℝ) (9/10 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨Cs, hCs, N, hN, hspec⟩ := ActualSharpSpectralCandidate.actual_spectralRatio_upper_uniform
  refine ⟨Cp + Cs, add_nonneg hCp hCs, ?_⟩
  filter_upwards [hpath, ActualExceptionalAssemblyCandidate.actual_maximizers_eventually_capped,
    eventually_ge_atTop N] with n hp hc hn
  obtain ⟨T, hT⟩ := ActualCoarseUpperClosureCandidate.exists_actual_maximizer n
  have hcap := hc T hT
  have h := hp T hcap.2.1 hcap.2.2
  have hs := hspec n hn T
  rw [hT] at h
  calc
    _ ≤ (lowerConstant + Cs / (n : ℝ)) + Cp / (n : ℝ) := by linarith
    _ = _ := by ring

theorem actual_all_pathCount_upper_uniform :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ T : Tournament n,
      (pathCount T : ℝ) / meanPaths n ≤ lowerConstant + C / (n : ℝ) := by
  obtain ⟨C, hC, hu⟩ := actual_maxPaths_upper_uniform
  refine ⟨C, hC, ?_⟩
  filter_upwards [hu] with n hn T
  have hm : 0 < meanPaths n := by unfold meanPaths; positivity
  have hp : (pathCount T : ℝ) ≤ maxPaths n := by exact_mod_cast pathCount_le_maxPaths T
  exact (div_le_div_of_nonneg_right hp hm.le).trans hn

theorem actual_maximizers_strong_upper_uniform :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ T : Tournament n,
      pathCount T = maxPaths n →
      (pathCount T : ℝ) / meanPaths n ≤
        lowerConstant * Real.exp (-tau (normalizedScore T)/2) + C / (n : ℝ) := by
  obtain ⟨Cp, hCp, hpath⟩ := ActualCappedPathUpperCandidate.actual_capped_path_upper
    (256 : ℝ) (9/10 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨Cs, hCs, N, hN, hspec⟩ := ActualSharpSpectralCandidate.actual_spectralRatio_upper_uniform
  refine ⟨Cp + Cs, add_nonneg hCp hCs, ?_⟩
  filter_upwards [hpath, ActualExceptionalAssemblyCandidate.actual_maximizers_eventually_capped,
    eventually_ge_atTop N] with n hp hc hn
  intro T hmax
  have hcap := hc T hmax
  have h := hp T hcap.2.1 hcap.2.2
  have he0 : 0 ≤ Real.exp (-tau (normalizedScore T)/2) := (Real.exp_pos _).le
  have he1 : Real.exp (-tau (normalizedScore T)/2) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    linarith [tau_nonneg (normalizedScore T)]
  have hs := mul_le_mul_of_nonneg_right (hspec n hn T) he0
  have herr := mul_le_mul_of_nonneg_left he1
    (div_nonneg hCs (Nat.cast_nonneg n : (0 : ℝ) ≤ n))
  calc
    _ ≤ (lowerConstant + Cs / (n : ℝ)) * Real.exp (-tau (normalizedScore T)/2) +
        Cp / (n : ℝ) := h.trans (add_le_add hs le_rfl)
    _ ≤ lowerConstant * Real.exp (-tau (normalizedScore T)/2) +
        (Cp + Cs) / (n : ℝ) := by rw [add_mul]; nlinarith [add_div Cp Cs (n : ℝ)]

theorem actual_maximizers_energy_O_inv :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ n : ℕ in atTop, ∀ T : Tournament n,
      pathCount T = maxPaths n → tau (normalizedScore T) ≤ D / (n : ℝ) := by
  obtain ⟨C, hC, hupper⟩ := actual_maximizers_strong_upper_uniform
  obtain ⟨Cr, hCr, N, hN, href⟩ := ActualMaxPathsLowerCandidate.actual_maxPaths_lower_uniform
  have hL : 0 < lowerConstant := lt_trans (by norm_num) ActualMaximizerEntryCandidate.lowerConstant_gt_one
  refine ⟨4 * (C + Cr) / lowerConstant, by positivity, ?_⟩
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hlim := hi.const_mul (C + Cr)
  simp only [mul_zero] at hlim
  filter_upwards [hupper, eventually_ge_atTop N, eventually_gt_atTop 0,
    hlim.eventually_le_const (by positivity : 0 < lowerConstant/2)] with n hu hnN hn hs
  intro T hmax
  have hm : 0 < meanPaths n := by unfold meanPaths; positivity
  have hlo : lowerConstant - Cr / (n : ℝ) ≤ (pathCount T : ℝ) / meanPaths n := by
    apply (le_div_iff₀ hm).mpr
    simpa only [hmax] using href n hnN
  have hh := EnergyMarginCandidate.energy_margin hL hL (by exact_mod_cast hn) hC hCr
    (by simpa only [div_eq_mul_inv] using hs) hlo (hu T hmax) (le_refl lowerConstant)
  rw [div_self hL.ne', Real.log_one, mul_zero, zero_add] at hh
  convert hh using 1; ring

theorem actual_maxPaths_abs_error_uniform :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      |(maxPaths n : ℝ) / meanPaths n - lowerConstant| ≤ C / (n : ℝ) := by
  obtain ⟨CL, hCL, NL, hNL, hL⟩ := ActualMaxPathsLowerCandidate.actual_maxPaths_lower_uniform
  obtain ⟨CU, hCU, hU⟩ := actual_maxPaths_upper_uniform
  obtain ⟨NU, hNU⟩ := Filter.eventually_atTop.mp hU
  refine ⟨CL + CU, add_nonneg hCL hCU, max NL (max NU 2), by omega, ?_⟩
  intro n hn
  have hm : 0 < meanPaths n := by unfold meanPaths; positivity
  have hlo : lowerConstant - CL / (n : ℝ) ≤ (maxPaths n : ℝ) / meanPaths n :=
    (le_div_iff₀ hm).mpr (hL n (by omega))
  have hup := hNU n (by omega)
  have hcL : 0 ≤ CL / (n : ℝ) := div_nonneg hCL (Nat.cast_nonneg n)
  have hcU : 0 ≤ CU / (n : ℝ) := div_nonneg hCU (Nat.cast_nonneg n)
  rw [add_div]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end ActualSharpPathEnergyCandidate
