import OperatorCapFocused
import ActualCappedPathUpperCandidate
import ActualExceptionalAssemblyCandidate
import ActualMaxPathsLowerCandidate

/-! Actual uniform two-constant closure. The capped path comparison is called
as a theorem, not supplied as an external premise. The packing constant U is
distinct from the reference constant L; this is not a sharp-L upper bound. -/
set_option autoImplicit false
noncomputable section
namespace ActualCoarseUpperClosureCandidate
open TournamentHamiltonian ActualTournamentPrescalingBounds TournamentPrescalingMassBound
open Filter
open scoped Classical Topology

lemma exists_actual_maximizer (n : ℕ) :
    ∃ T : Tournament n, pathCount T = maxPaths n := by
  have hne : (Finset.univ : Finset (Tournament n)).Nonempty :=
    ⟨transitiveTournament n, Finset.mem_univ _⟩
  obtain ⟨T, _, hT⟩ := Finset.exists_mem_eq_sup Finset.univ hne (pathCount (n := n))
  exact ⟨T, hT.symm⟩

/-- The actual maximum has the packing upper constant with one uniform O(1/n)
error. Neither a capped path estimate nor any score/spectral cap is a premise. -/
theorem actual_maxPaths_upper_uniform :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      (maxPaths n : ℝ)/meanPaths n ≤ upperConstant+C/(n : ℝ) := by
  obtain ⟨C, hC, hpath⟩ :=
    ActualCappedPathUpperCandidate.actual_capped_path_upper_weak
      (256 : ℝ) (9/10 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hpath, ActualExceptionalAssemblyCandidate.actual_maximizers_eventually_capped,
    eventually_ge_atTop (2 : ℕ)] with n hpath hcap hn
  obtain ⟨T, hT⟩ := exists_actual_maximizer n
  have hc := hcap T hT
  have hp := hpath T hc.2.1 hc.2.2
  have hr := spectralRatio_le_upperConstant T (by omega)
  rw [hT] at hp
  exact hp.trans (add_le_add hr le_rfl)

/-- Every actual tournament inherits the uniform upper bound from the finite
maximum, without imposing a score cap on the arbitrary tournament. -/
theorem actual_all_pathCount_upper_uniform :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ T : Tournament n,
      (pathCount T : ℝ)/meanPaths n ≤ upperConstant+C/(n : ℝ) := by
  obtain ⟨C, hC, hu⟩ := actual_maxPaths_upper_uniform
  refine ⟨C, hC, ?_⟩
  filter_upwards [hu] with n hn T
  have hm : 0 < meanPaths n := by unfold meanPaths; positivity
  have hp : (pathCount T : ℝ) ≤ maxPaths n := by exact_mod_cast pathCount_le_maxPaths T
  exact (div_le_div_of_nonneg_right hp hm.le).trans hn

/-- The repository's original MainBound, with the genuine reference lower L
and the distinct packing upper U, one common nonnegative error constant and
one common n≥2 threshold. There is no external path-comparison premise. -/
theorem actual_mainBound : MainBound := by
  obtain ⟨CL, hCL, NL, hNL, hL⟩ := ActualMaxPathsLowerCandidate.actual_maxPaths_lower_uniform
  obtain ⟨CU, hCU, hU⟩ := actual_maxPaths_upper_uniform
  obtain ⟨NU, hNU⟩ := Filter.eventually_atTop.mp hU
  unfold MainBound
  refine ⟨CL+CU, add_nonneg hCL hCU, max NL (max NU 2), by omega, ?_⟩
  intro n hn
  have hnL : NL ≤ n := by omega
  have hnU : NU ≤ n := by omega
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hm : 0 < meanPaths n := by unfold meanPaths; positivity
  have hdL : CL/(n : ℝ) ≤ (CL+CU)/(n : ℝ) :=
    div_le_div_of_nonneg_right (by linarith) hn0.le
  have hdU : CU/(n : ℝ) ≤ (CL+CU)/(n : ℝ) :=
    div_le_div_of_nonneg_right (by linarith) hn0.le
  constructor
  · exact (mul_le_mul_of_nonneg_right (by linarith) hm.le).trans (hL n hnL)
  · have hu := (div_le_iff₀ hm).mp (hNU n hnU)
    exact hu.trans (mul_le_mul_of_nonneg_right (by linarith) hm.le)

end ActualCoarseUpperClosureCandidate

set_option pp.fullNames true
#check ActualCoarseUpperClosureCandidate.exists_actual_maximizer
#print axioms ActualCoarseUpperClosureCandidate.exists_actual_maximizer
#check ActualCoarseUpperClosureCandidate.actual_maxPaths_upper_uniform
#print axioms ActualCoarseUpperClosureCandidate.actual_maxPaths_upper_uniform
#check ActualCoarseUpperClosureCandidate.actual_all_pathCount_upper_uniform
#print axioms ActualCoarseUpperClosureCandidate.actual_all_pathCount_upper_uniform
#check ActualCoarseUpperClosureCandidate.actual_mainBound
#print axioms ActualCoarseUpperClosureCandidate.actual_mainBound
