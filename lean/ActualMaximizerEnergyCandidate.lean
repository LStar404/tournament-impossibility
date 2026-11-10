import EnergyMarginCandidate
import ActualCappedPathUpperCandidate
import ActualExceptionalAssemblyCandidate
import ActualMaxPathsLowerCandidate
import ActualMaximizerEntryCandidate
import OperatorCapFocused
/-! Actual maximizer energy bound from the accepted strong path upper. -/
set_option autoImplicit false
noncomputable section
namespace ActualMaximizerEnergyCandidate
open TournamentHamiltonian ActualTournamentPrescalingBounds TournamentPrescalingMassBound
open Filter
open scoped Topology

theorem actual_maximizers_eventually_bounded_energy :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ n : ℕ in atTop, ∀ T : Tournament n,
      pathCount T = maxPaths n →
      tau (normalizedScore T) ≤ 2*Real.log (upperConstant/lowerConstant)+D/(n:ℝ) := by
  obtain ⟨C,hC,hupper⟩ := ActualCappedPathUpperCandidate.actual_capped_path_upper
    256 (9/10) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨Cr,hCr,N,hN,href⟩ := ActualMaxPathsLowerCandidate.actual_maxPaths_lower_uniform
  have hL : 0 < lowerConstant := lt_trans (by norm_num) ActualMaximizerEntryCandidate.lowerConstant_gt_one
  refine ⟨4*(C+Cr)/lowerConstant, by positivity, ?_⟩
  have hi : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hlim := hi.const_mul (C+Cr)
  simp only [mul_zero] at hlim
  filter_upwards [hupper, ActualExceptionalAssemblyCandidate.actual_maximizers_eventually_capped,
    eventually_ge_atTop N, eventually_gt_atTop 0,
    hlim.eventually_le_const (by positivity : 0 < lowerConstant/2)] with n hu hc hnN hn hs
  intro T hmax
  have hcap := hc T hmax
  have hm : 0 < meanPaths n := by unfold meanPaths; positivity
  have hlo : lowerConstant-Cr/(n:ℝ) ≤ (pathCount T:ℝ)/meanPaths n := by
    apply (le_div_iff₀ hm).mpr
    simpa only [hmax] using href n hnN
  have hup := hu T hcap.2.1 hcap.2.2
  have hU : 0 < upperConstant :=
    lt_of_lt_of_le (spectralRatio_bounds T hn).1 (spectralRatio_le_upperConstant T hn)
  have hh := EnergyMarginCandidate.energy_margin hL hU (by exact_mod_cast hn) hC hCr
    (by simpa only [div_eq_mul_inv] using hs) hlo hup (spectralRatio_le_upperConstant T hn)
  convert hh using 1; ring
end ActualMaximizerEnergyCandidate
