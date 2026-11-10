import ActualCutoffMinorLowerCandidate
import UnitGeneratingAdditive
set_option autoImplicit false
noncomputable section
namespace ActualUnitPathLowerCandidate
open Filter TournamentHamiltonian
open scoped Topology

def pathErrorConstant : ℝ :=
  6*Real.exp 1*Real.exp (1/2)+UnitMinorErrorBudgetCandidate.lowerConstant*principalErrorMomentConstant+1

lemma pathErrorConstant_nonneg : 0 ≤ pathErrorConstant := by
  have hc := UnitMinorErrorBudgetCandidate.constants_nonneg.2.2
  have hM := principalErrorMomentConstant_nonneg
  unfold pathErrorConstant
  positivity

theorem eventually_actual_unit_path_lower :
    ∀ᶠ n : ℕ in atTop, ∀ T : Tournament n, (∀ i,|score T i|≤1) →
      spectralRatio T-pathErrorConstant/(n:ℝ) ≤ (pathCount T:ℝ)/meanPaths n := by
  filter_upwards [ActualCutoffMinorLowerCandidate.eventually_cutoff_signed_minor_lower,
    principal_subset_tail_eventually_le_inverse, eventually_gt_atTop 0] with n hp ht hn
  intro T hs
  have hb := pathCount_spectral_lower_from_signed_minors T hn
    UnitMinorErrorBudgetCandidate.lowerConstant (6*Real.exp 1*Real.exp (1/2))
    UnitMinorErrorBudgetCandidate.constants_nonneg.2.2 (by positivity)
    (unit_generating_additive T hn hs) (by simpa only [pathLowerPermanentFactor] using hp T hs)
  unfold pathErrorConstant
  have he : (6*Real.exp 1*Real.exp (1/2)+UnitMinorErrorBudgetCandidate.lowerConstant*principalErrorMomentConstant+1)/(n:ℝ) =
      (6*Real.exp 1*Real.exp (1/2)+UnitMinorErrorBudgetCandidate.lowerConstant*principalErrorMomentConstant)/(n:ℝ)+1/(n:ℝ) := by ring
  rw [he]
  linarith

theorem actual_unit_path_lower_uniform :
    ∃ C : ℝ,0≤C ∧ ∃ N : ℕ,2≤N ∧ ∀ n : ℕ,N≤n →
      ∀ T : Tournament n,(∀ i,|score T i|≤1) →
        spectralRatio T-C/(n:ℝ) ≤ (pathCount T:ℝ)/meanPaths n := by
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp eventually_actual_unit_path_lower
  exact ⟨pathErrorConstant,pathErrorConstant_nonneg,max N 2,by omega,
    fun n hn => hN n (by omega)⟩
end ActualUnitPathLowerCandidate
