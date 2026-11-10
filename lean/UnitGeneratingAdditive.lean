import SmallScoreGeneratingLowerFocused
import CrudeSkewDetBound

namespace TournamentHamiltonian
theorem unit_generating_additive {n : ℕ} (T : Tournament n)
    (hn : 0 < n) (hscore : ∀ i, |score T i| ≤ 1) :
    2 * Real.exp 1 * ((1 : Matrix (Fin n) (Fin n) ℝ) + (1 / (n : ℝ)) • signMatrix T).det -
      (6 * Real.exp 1 * Real.exp (1 / 2 : ℝ)) / n ≤
      ((1 : Matrix (Fin n) (Fin n) ℝ) + (2 / (n : ℝ)) • (1 + adjacency T)).det := by
  have h := tournament_generating_det_lower_unit_scores T hn hscore
  have hd := tournament_skew_kernel_det_le_exp_half T hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hh := mul_le_mul_of_nonneg_left hd (show 0 ≤ 6 * Real.exp 1 / (n : ℝ) by positivity)
  ring_nf at h hh ⊢
  linarith
end TournamentHamiltonian

namespace TournamentHamiltonian
end TournamentHamiltonian
