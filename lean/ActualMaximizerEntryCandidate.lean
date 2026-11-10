import GlobalEntryFiniteCandidate
import ActualMaxPathsLowerCandidate
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! Actual maximizer low-energy entrance from the proved reference lower bound. -/
set_option autoImplicit false
noncomputable section
namespace ActualMaximizerEntryCandidate
open TournamentHamiltonian ActualTournamentPrescalingBounds TournamentPrescalingMassBound
open Filter
open scoped Topology

lemma lowerConstant_gt_one : 1 < TournamentHamiltonian.lowerConstant := by
  have hcos : 0 < Real.cos 1 := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_gt_three]
  have hcosh : 1 < Real.cosh 1 := Real.one_lt_cosh.mpr (by norm_num)
  unfold TournamentHamiltonian.lowerConstant
  apply (lt_div_iff₀ hcos).mpr
  simpa using (Real.cos_le_one 1).trans_lt hcosh

/-- The actual reference lower bound and L>1 establish competition with the
averaging benchmark, without any external path-count lower assumption. -/
theorem maxPaths_eventually_ge_mean :
    ∀ᶠ n : ℕ in atTop, meanPaths n ≤ (maxPaths n : ℝ) := by
  obtain ⟨C, _hC, N, _hN, hbound⟩ :=
    ActualMaxPathsLowerCandidate.actual_maxPaths_lower_uniform
  have hzero : Tendsto (fun n : ℕ => C / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop N,
    hzero.eventually_lt_const (sub_pos.mpr lowerConstant_gt_one)] with n hn hsmall
  have hfactor : 1 ≤ TournamentHamiltonian.lowerConstant-C/(n:ℝ) := by linarith
  have hm : 0 ≤ meanPaths n := by unfold meanPaths; positivity
  calc
    meanPaths n = 1*meanPaths n := (one_mul _).symm
    _ ≤ (TournamentHamiltonian.lowerConstant-C/(n:ℝ))*meanPaths n :=
      mul_le_mul_of_nonneg_right hfactor hm
    _ ≤ (maxPaths n : ℝ) := hbound n hn

/-- Every actual maximizer lies in the logarithmic degree/score-energy regime.
No external H>=mean, minor estimate, or final asymptotic is a premise. -/
theorem actual_maximizers_eventually_lowVariance :
    ∀ᶠ n : ℕ in atTop, ∀ T : Tournament n,
      pathCount T = maxPaths n →
      degreeVariance T < 16*(n:ℝ)^2*Real.log n ∧
      tau (normalizedScore T) ≤ 256*Real.log (n:ℝ) := by
  filter_upwards [GlobalEntryFiniteCandidate.competitive_eventually_lowVariance,
    maxPaths_eventually_ge_mean] with n hvariance hmean
  intro T hmax
  apply hvariance T
  simpa only [hmax] using hmean

end ActualMaximizerEntryCandidate
set_option pp.fullNames true
#check ActualMaximizerEntryCandidate.lowerConstant_gt_one
#print axioms ActualMaximizerEntryCandidate.lowerConstant_gt_one
#check ActualMaximizerEntryCandidate.maxPaths_eventually_ge_mean
#print axioms ActualMaximizerEntryCandidate.maxPaths_eventually_ge_mean
#check ActualMaximizerEntryCandidate.actual_maximizers_eventually_lowVariance
#print axioms ActualMaximizerEntryCandidate.actual_maximizers_eventually_lowVariance
