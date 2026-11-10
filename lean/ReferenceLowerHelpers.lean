import TournamentHamiltonian.HighVariance
import PrincipalLowerMomentsFocused
import TournamentHamiltonian.SkewSpectrum

namespace TournamentHamiltonian
open Filter
open scoped Topology
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

theorem shortConvolution_le_pathCount {n : ℕ} (T : Tournament n) (K : ℕ) :
    shortConvolution T K≤(pathCount T : ℝ) := by
  have h := shortConvolution_add_longConvolution T K
  linarith [longConvolution_nonneg T K]

noncomputable def pathLowerPermanentFactor {n : ℕ} (T : Tournament n) : ℝ := Real.exp (-1)*gaussianFactor T

theorem pathLowerPermanentFactor_bounds {n : ℕ} (T : Tournament n) (hn : 0<n) :
    0≤pathLowerPermanentFactor T ∧ pathLowerPermanentFactor T/2≤1 := by
  obtain ⟨hG,hG2⟩ := gaussianFactor_bounds T hn
  have he : Real.exp (-1)≤1 := Real.exp_le_one_iff.mpr (by norm_num)
  constructor
  · exact mul_nonneg (Real.exp_pos _).le hG.le
  · unfold pathLowerPermanentFactor
    have h := mul_le_mul he hG2.le hG.le (by norm_num : (0 : ℝ)≤1)
    nlinarith

theorem principal_subset_tail_eventually_le_inverse :
    ∀ᶠ n : ℕ in atTop,subsetTailAt 1 n≤1/(n : ℝ) := by
  have h := scaled_subsetTail_eventually_small (by norm_num : (0 : ℝ)<1) 2 (by norm_num : (0 : ℝ)<1)
  filter_upwards [h] with n hn
  norm_num only at hn
  simp only [one_mul] at hn
  have hs : 1≤Real.sqrt ((n : ℝ)+1) := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (by linarith [Nat.cast_nonneg (α := ℝ) n] : (1 : ℝ)≤n+1)
  have ht : 0≤subsetTailAt 1 n := by
    unfold subsetTailAt
    exact tsum_nonneg (fun k=>mul_nonneg (by positivity) (subsetWeight_nonneg _))
  have hb := mul_le_mul_of_nonneg_right hs ht
  simp only [one_mul] at hb
  exact hb.trans hn

end TournamentHamiltonian

namespace TournamentHamiltonian
open Filter
open scoped Topology
end TournamentHamiltonian
