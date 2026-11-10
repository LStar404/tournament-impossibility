import SpectralMomentBridgeCandidate
import OddMomentRatioComparisonCandidate
import OperatorCapFocused

/-!
Isolated sharp spectral comparison and quantitative reference adapter.
This does not assert the path-count closure or score-energy stability.
Compilation/audit state is recorded separately in build/SHARP_STATUS.json.
-/

namespace ActualSharpSpectralCandidate
open TournamentHamiltonian

/-- Sharp finite-order spectral comparison for every actual tournament. -/
theorem actual_spectralRatio_le_transitive {n : ℕ} (T : Tournament n)
    (hn : 0 < n) :
    spectralRatio T ≤ spectralRatio (transitiveTournament n) := by
  rw [spectralRatio_eq_paired_product T hn,
    spectralRatio_eq_paired_product (transitiveTournament n) hn]
  apply OddMomentRatioComparisonCandidate.ratio_product_le_of_positive_moments
  · intro x hx
    exact ⟨pairedMasses_nonneg T x hx,
      lt_trans (pairedMasses_lt_half T hn x hx) (by norm_num)⟩
  · intro x hx
    exact ⟨pairedMasses_nonneg (transitiveTournament n) x hx,
      lt_trans (pairedMasses_lt_half (transitiveTournament n) hn x hx) (by norm_num)⟩
  · intro r hr
    exact SpectralMomentBridgeCandidate.paired_moments_le_transitive T hn r (by omega)

/-- Reuse the existing complex transitive determinant-ratio rate. -/
theorem transitive_spectralRatio_eq (n : ℕ) (hn : 0 < n) :
    (spectralRatio (transitiveTournament n) : ℂ) = transitiveRatio n := by
  rw [← determinantRatio_eq_spectralRatio (transitiveTournament n) hn,
    determinantRatio, complexSignMatrix_transitiveTournament]
  rfl

theorem transitive_spectralRatio_error_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      |spectralRatio (transitiveTournament n) - lowerConstant| ≤ C / n := by
  obtain ⟨C, hC, N, hN, hbound⟩ := transitiveRatio_error_bound
  refine ⟨C, hC, N, hN, ?_⟩
  intro n hn
  have hn0 : 0 < n := by omega
  have h := hbound n hn
  rw [← transitive_spectralRatio_eq n hn0] at h
  simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using h

/-- Uniform sharp-L spectral upper bound; no score or maximizer assumption. -/
theorem actual_spectralRatio_upper_uniform :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, 1 ≤ N ∧
      ∀ n : ℕ, N ≤ n → ∀ T : Tournament n,
        spectralRatio T ≤ lowerConstant + C / n := by
  obtain ⟨C, hC, N, hN, hbound⟩ := transitive_spectralRatio_error_bound
  refine ⟨C, hC, N, hN, ?_⟩
  intro n hn T
  have hcmp := actual_spectralRatio_le_transitive T (by omega)
  have hupper := (abs_le.mp (hbound n hn)).2
  linarith

end ActualSharpSpectralCandidate

#print axioms ActualSharpSpectralCandidate.actual_spectralRatio_le_transitive
#print axioms ActualSharpSpectralCandidate.transitive_spectralRatio_eq
#print axioms ActualSharpSpectralCandidate.transitive_spectralRatio_error_bound
#print axioms ActualSharpSpectralCandidate.actual_spectralRatio_upper_uniform
