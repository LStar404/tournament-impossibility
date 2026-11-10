import SkewGaussianActualNormCandidate

/-! Isolated verified endpoint. Actual skew Gaussian-log baseline O(1/n).
This is a determinant-log theorem, not an assumed Gaussian integral identity.
It does not remove any Γ term from separate recovery/error estimates. -/
set_option autoImplicit false
noncomputable section
namespace SkewGaussianBaselineCandidate
open Matrix
open SkewBaselineGramDifferenceCandidate SkewGaussianFactorCandidate
open SkewGaussianActualNormCandidate PositiveGramLogDetCandidate
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}

/-- No spectral cap is assumed: all hypotheses concern actual S and its entries. -/
theorem actual_gaussian_baseline (hn : 24 ≤ n)
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : Sᵀ = -S) (he : ∀ i j, |S i j| ≤ 1) :
    0 < (1-(scaled S)ᵀ*scaled S).det ∧
    0 < (1-(shifted S)ᵀ*shifted S).det ∧
    ‖gaussianLog ((shifted S)ᵀ*shifted S)-gaussianLog ((scaled S)ᵀ*scaled S)‖ ≤
      19/(n:ℝ) := by
  have hc := actual_common_norm_caps hn S hS he
  have hh := gaussian_bound_of_norm_caps (by omega) S hS he (19/23)
    (by norm_num) (by norm_num) hc.1 hc.2
  have hnR : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  refine ⟨hh.1, hh.2.1, hh.2.2.trans ?_⟩
  have hconst : (2:ℝ)*(1-(19/23)^2) = 336/529 := by norm_num
  rw [hconst, div_div]
  apply (div_le_div_iff₀ (mul_pos hnR (by norm_num)) hnR).mpr
  nlinarith

/-- The matching logdet difference includes the Gaussian factor of two. -/
theorem actual_logdet_baseline (hn : 24 ≤ n)
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : Sᵀ = -S) (he : ∀ i j, |S i j| ≤ 1) :
    ‖Real.log (1-(shifted S)ᵀ*shifted S).det-
      Real.log (1-(scaled S)ᵀ*scaled S).det‖ ≤ 38/(n:ℝ) := by
  have hh := (actual_gaussian_baseline hn S hS he).2.2
  have hx : Real.log (1-(shifted S)ᵀ*shifted S).det-
      Real.log (1-(scaled S)ᵀ*scaled S).det =
      -2*(gaussianLog ((shifted S)ᵀ*shifted S)-gaussianLog ((scaled S)ᵀ*scaled S)) := by
    unfold gaussianLog
    ring
  rw [hx, norm_mul]
  rw [show ‖(-2:ℝ)‖ = 2 by norm_num]
  calc
    _ ≤ 2*(19/(n:ℝ)) := mul_le_mul_of_nonneg_left hh (by norm_num)
    _ = 38/(n:ℝ) := by ring

end SkewGaussianBaselineCandidate
