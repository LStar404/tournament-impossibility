import SkewBaselineGramDifferenceCandidate
import PositiveGramLogDetCandidate

/-! Isolated verified factor layer. See Audit.log for type and axiom checks.
The factor is genuinely Fin (2*n) by Fin n, not a square factor hypothesis.
All matrix norms below are explicitly the Euclidean L2 operator norm. -/
set_option autoImplicit false
noncomputable section
namespace SkewGaussianFactorCandidate
open Matrix Finset
open SkewBaselineGramDifferenceCandidate
open scoped Matrix.Norms.L2Operator BigOperators
variable {n : ℕ}

/-- Explicit identification of the two stacked row blocks with Fin (2*n). -/
def rowEquiv (n : ℕ) : Fin (2*n) ≃ Fin n ⊕ Fin n :=
  (finCongr (two_mul n)).trans finSumFinEquiv.symm

def stacked (S : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n ⊕ Fin n) (Fin n) ℝ :=
  Matrix.fromRows (Real.sqrt (coefficient n) • S)
    (((n:ℝ)-1)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ))

def factor (S : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin (2*n)) (Fin n) ℝ :=
  (stacked S).submatrix (rowEquiv n) id

lemma factor_gram (hn : 2 ≤ n) (S : Matrix (Fin n) (Fin n) ℝ) :
    (factor S)ᵀ*factor S =
      coefficient n • (Sᵀ*S)+(((n:ℝ)-1)⁻¹)^2 • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  unfold factor
  rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
  unfold stacked
  rw [Matrix.transpose_fromRows, Matrix.fromCols_mul_fromRows]
  simp only [Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, Matrix.one_mul]
  rw [Real.mul_self_sqrt (coefficient_nonneg hn)]
  simp only [pow_two]

theorem actual_factorization (hn : 2 ≤ n) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : Sᵀ = -S) :
    (shifted S)ᵀ*shifted S-(scaled S)ᵀ*scaled S = (factor S)ᵀ*factor S := by
  change loss S = _
  rw [loss_exact S hS, factor_gram hn S]

/-- The rectangular Frobenius *square* is precisely the trace loss. -/
lemma factor_frob_eq_trace (hn : 2 ≤ n) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : Sᵀ = -S) : RealGramEndpoint.frob (factor S) = (loss S).trace := by
  have ht : ((factor S)ᵀ*factor S).trace = RealGramEndpoint.frob (factor S) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply,
      RealGramEndpoint.frob]
    rw [Finset.sum_comm]
    simp only [pow_two]
  rw [← ht]
  congr 1
  exact (actual_factorization hn S hS).symm

theorem factor_frob_bound (hn : 2 ≤ n) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : Sᵀ = -S) (he : ∀ i j, |S i j| ≤ 1) :
    0 ≤ RealGramEndpoint.frob (factor S) ∧
      RealGramEndpoint.frob (factor S) ≤ 12/(n:ℝ) := by
  rw [factor_frob_eq_trace hn S hS]
  exact trace_loss_bound hn S hS he

lemma gram_norm_le_square (A : Matrix (Fin n) (Fin n) ℝ) (q : ℝ)
    (hq : 0 ≤ q) (hA : ‖A‖ ≤ q) : ‖Aᵀ*A‖ ≤ q^2 := by
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial A,
    Matrix.l2_opNorm_conjTranspose_mul_self, pow_two]
  exact mul_le_mul hA hA (norm_nonneg _) hq

/-- First-stage endpoint: actual skew factorization, with explicit norm caps. -/
theorem gaussian_bound_of_norm_caps (hn : 2 ≤ n)
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : Sᵀ = -S) (he : ∀ i j, |S i j| ≤ 1)
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (hC : ‖scaled S‖ ≤ q) (hZ : ‖shifted S‖ ≤ q) :
    0 < (1-(scaled S)ᵀ*scaled S).det ∧
    0 < (1-(shifted S)ᵀ*shifted S).det ∧
    ‖PositiveGramLogDetCandidate.gaussianLog ((shifted S)ᵀ*shifted S)-
      PositiveGramLogDetCandidate.gaussianLog ((scaled S)ᵀ*scaled S)‖ ≤
      (12/(n:ℝ))/(2*(1-q^2)) := by
  have hh := PositiveGramLogDetCandidate.positive_gaussian_factor_bound
    ((scaled S)ᵀ*scaled S) ((shifted S)ᵀ*shifted S) (factor S)
    (actual_factorization hn S hS) q hq hq1
    (gram_norm_le_square (scaled S) q hq hC)
    (gram_norm_le_square (shifted S) q hq hZ)
  refine ⟨hh.1, hh.2.1, hh.2.2.trans ?_⟩
  apply div_le_div_of_nonneg_right (factor_frob_bound hn S hS he).2
  nlinarith

end SkewGaussianFactorCandidate
