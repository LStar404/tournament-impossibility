import MeetingConvolutionFinite
import ExceptionalCoreGeometryCandidate
import LogWindowErrorCandidate
set_option autoImplicit false
/-! Actual exceptional meeting-short convolution is absolutely o(meanPaths).
No permanent approximation, core-minor estimate, or final path bound is assumed. -/
namespace TournamentHamiltonian
open scoped Classical Topology
open Filter
theorem exceptional_meeting_convolution_eventually_small (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop, ∀ T : Tournament n,
      degreeVariance T < 16 * (n : ℝ) ^ 2 * Real.log n →
      meetingShortConvolution T (exceptionalVertices T) (subsetCutoff n) / meanPaths n ≤ eps := by
  let C : ℝ := 400 * Real.exp 7 * subsetWeightMass
  have hC : 0 ≤ C := by dsimp [C]; exact mul_nonneg (by positivity) subsetWeightMass_nonneg
  have hlim := (LogWindowErrorCandidate.log_sqrt_decay 2).const_mul C
  simp only [mul_zero] at hlim
  filter_upwards [hlim.eventually_le_const heps, short_cutoff_eventually_small] with n he hn T hV
  have hn2 : 2 ≤ n := by omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  have hs0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR
  have hf := exceptionalVertices_card_le_log T hn2 hV
  have hk := hn.2.1
  have hprod := mul_le_mul hf hk (by positivity : 0 ≤ (subsetCutoff n : ℝ)) (by positivity : 0 ≤ 400 * Real.log (n : ℝ))
  have hs : Real.sqrt ((n : ℝ) + 1) ≤ 2 * Real.sqrt n := by
    nlinarith [Real.sq_sqrt (show 0 ≤ (n : ℝ) + 1 by positivity), Real.sq_sqrt hn0.le,
      Real.sqrt_nonneg ((n : ℝ) + 1), Real.sqrt_nonneg (n : ℝ)]
  apply (meetingShortConvolution_normalized_le T (exceptionalVertices T) (subsetCutoff n) (by omega)).trans
  apply le_trans _ he
  have hp := div_le_div_of_nonneg_right hprod hn0.le
  have h := mul_le_mul hp hs (Real.sqrt_nonneg ((n : ℝ) + 1)) (by positivity : 0 ≤ 400 * Real.log (n : ℝ) * Real.log (n : ℝ) / n)
  have hh := mul_le_mul_of_nonneg_right h (mul_nonneg (by positivity : 0 ≤ Real.exp 7 / 2) subsetWeightMass_nonneg)
  have heq : (400 * Real.log (n : ℝ) * Real.log (n : ℝ) / n * (2 * Real.sqrt n)) *
      ((Real.exp 7 / 2) * subsetWeightMass) = C * (Real.log (n : ℝ) ^ 2 / Real.sqrt n) := by
    dsimp [C]
    field_simp
    rw [Real.sq_sqrt hn0.le]
  rw [heq] at hh
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hh


end TournamentHamiltonian

set_option pp.fullNames true
#check TournamentHamiltonian.exceptional_meeting_convolution_eventually_small
#print axioms TournamentHamiltonian.exceptional_meeting_convolution_eventually_small
