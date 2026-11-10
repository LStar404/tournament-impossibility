import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.Trace

/-! Verified in the 557-module direct-Lean compilation and declaration audit.
Finite baseline comparison. No logdet integral claim.
Real matrices avoid any hidden conjugation or norm-instance conversion. -/
set_option autoImplicit false
noncomputable section
namespace SkewBaselineGramDifferenceCandidate
open Matrix Finset
variable {n : ℕ}

def shifted (S : Matrix (Fin n) (Fin n) ℝ) := ((n:ℝ)-1)⁻¹ • (S-1)
def scaled (S : Matrix (Fin n) (Fin n) ℝ) := (n:ℝ)⁻¹ • S
def loss (S : Matrix (Fin n) (Fin n) ℝ) :=
  (shifted S).transpose*shifted S-(scaled S).transpose*scaled S

def coefficient (n : ℕ) : ℝ := (((n:ℝ)-1)⁻¹)^2-((n:ℝ)⁻¹)^2

lemma coefficient_nonneg (hn : 2 ≤ n) : 0 ≤ coefficient n := by
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have ha : 0 < (n:ℝ)-1 := by linarith
  have hb : 0 < (n:ℝ) := by linarith
  have hi : (n:ℝ)⁻¹ ≤ ((n:ℝ)-1)⁻¹ := inv_anti₀ ha (by linarith)
  unfold coefficient
  nlinarith [inv_nonneg.mpr hb.le, inv_nonneg.mpr ha.le]

lemma shifted_gram (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.transpose = -S) :
    (S-1).transpose*(S-1) = S.transpose*S+1 := by
  rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.mul_sub, Matrix.one_mul, Matrix.one_mul, Matrix.mul_one]
  rw [hS]
  abel

lemma loss_exact (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.transpose = -S) :
    loss S = coefficient n • (S.transpose*S)+(((n:ℝ)-1)⁻¹)^2 • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  unfold loss shifted scaled
  simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [shifted_gram S hS]
  unfold coefficient
  simp only [smul_add, sub_smul, pow_two]
  abel

theorem loss_posSemidef (hn : 2 ≤ n) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : S.transpose = -S) : (loss S).PosSemidef := by
  rw [loss_exact S hS]
  have hg : (S.transpose*S).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.posSemidef_conjTranspose_mul_self S
  exact (hg.smul (coefficient_nonneg hn)).add (Matrix.PosSemidef.one.smul (sq_nonneg _))

lemma trace_gram (S : Matrix (Fin n) (Fin n) ℝ) :
    (S.transpose*S).trace = ∑ i,∑ j,(S i j)^2 := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  simp only [pow_two]

lemma trace_loss_exact (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.transpose = -S) :
    (loss S).trace = coefficient n*(∑ i,∑ j,(S i j)^2)+(((n:ℝ)-1)⁻¹)^2*(n:ℝ) := by
  rw [loss_exact S hS, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
    trace_gram, Matrix.trace_one]
  simp

/-- Coarse bound is enough for the sharp O(1/n), not O(1/sqrt n), baseline step. -/
theorem trace_loss_bound (hn : 2 ≤ n) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : S.transpose = -S) (he : ∀ i j,|S i j| ≤ 1) :
    0 ≤ (loss S).trace ∧ (loss S).trace ≤ 12/(n:ℝ) := by
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n:ℝ) := by linarith
  have hd : 0 < (n:ℝ)-1 := by linarith
  have hg0 : 0 ≤ ∑ i,∑ j,(S i j)^2 := sum_nonneg (fun i _ => sum_nonneg (fun j _ => sq_nonneg _))
  have hg : (∑ i,∑ j,(S i j)^2) ≤ (n:ℝ)^2 := by
    calc
      _ ≤ ∑ _i : Fin n,∑ _j : Fin n,(1:ℝ) := by
        apply sum_le_sum
        intro i hi
        apply sum_le_sum
        intro j hj
        exact (sq_le_one_iff_abs_le_one _).mpr (he i j)
      _ = _ := by simp; ring
  rw [trace_loss_exact S hS]
  constructor
  · exact add_nonneg (mul_nonneg (coefficient_nonneg hn) hg0) (mul_nonneg (sq_nonneg _) hn0.le)
  · calc
      _ ≤ coefficient n*(n:ℝ)^2+(((n:ℝ)-1)⁻¹)^2*(n:ℝ) := by
        exact add_le_add (mul_le_mul_of_nonneg_left hg (coefficient_nonneg hn)) le_rfl
      _ = (3*(n:ℝ)-1)/((n:ℝ)-1)^2 := by
        unfold coefficient
        field_simp
        ring
      _ ≤ 12/(n:ℝ) := by
        apply (div_le_div_iff₀ (sq_pos_of_pos hd) hn0).mpr
        nlinarith [sq_nonneg ((n:ℝ)-2)]
end SkewBaselineGramDifferenceCandidate
