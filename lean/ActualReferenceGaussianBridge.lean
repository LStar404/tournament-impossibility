import TournamentHamiltonian.SkewSpectrum
import GaussianExponentialCandidate
import SkewBaselineGramDifferenceCandidate
noncomputable section
namespace ActualReferenceGaussianBridge
open TournamentHamiltonian Matrix
lemma skewGram_identity {n : ℕ} (T : Tournament n) :
    skewGram T = 1 - (SkewBaselineGramDifferenceCandidate.scaled (signMatrix T))ᵀ *
      SkewBaselineGramDifferenceCandidate.scaled (signMatrix T) := by
  simp only [skewGram, SkewBaselineGramDifferenceCandidate.scaled, Matrix.transpose_smul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 2
  simp [div_eq_mul_inv, pow_two]
lemma gaussianFactor_eq_exp_g {n : ℕ} (T : Tournament n) (hn : 0 < n) :
    gaussianFactor T = Real.exp (RealProjectionAggregationCandidate.g
      (SkewBaselineGramDifferenceCandidate.scaled (signMatrix T))) := by
  unfold gaussianFactor
  rw [skewGram_identity]
  exact GaussianExponentialCandidate.gaussian_main_eq_exp _ (by
    rw [←skewGram_identity]; exact skewGram_det_pos T hn)
lemma one_le_gaussianFactor {n : ℕ} (T : Tournament n) (hn : 0 < n) :
    1 ≤ gaussianFactor T := by
  rw [gaussianFactor_eq_product T hn]
  have hp := complexSignMatrix_imaginary_det_pos T hn
  have hprod : ∀ xs : List ℝ, (∀ x ∈ xs, 0 ≤ x ∧ x ≤ 1) → xs.prod ≤ 1 := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih =>
      intro hx
      have h0 := hx x (by simp)
      have hh := ih (fun y hy => hx y (by simp [hy]))
      simpa using (mul_le_mul_of_nonneg_left hh h0.1).trans (by simpa using h0.2)
  have hle := hprod ((pairedMasses T).map (fun x => 1-x)) (by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
    have h0 := pairedMasses_nonneg T y hy
    have h1 := pairedMasses_lt_half T hn y hy
    constructor <;> linarith)
  exact (one_le_inv₀ hp).mpr hle
end ActualReferenceGaussianBridge
