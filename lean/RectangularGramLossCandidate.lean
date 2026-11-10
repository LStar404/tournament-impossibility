import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Complex.Norm

/-! Verified in the 557-module direct-Lean compilation and declaration audit. Finite rectangular projection Gram loss only.
No log determinant, asymptotic window, tournament, or extremality assertion.
Matrix norms are deliberately absent: frobeniusSq is an explicit entry sum.
For later operator estimates use Matrix.Norms.L2Operator explicitly. -/
set_option autoImplicit false
noncomputable section
namespace RectangularGramLossCandidate
open Matrix
open scoped BigOperators ComplexOrder
variable {r c : ℕ}

def frobeniusSq (Z : Matrix (Fin r) (Fin c) ℂ) : ℝ :=
  ∑ i, ∑ j, ‖Z i j‖ ^ 2

def gramLoss (Z : Matrix (Fin r) (Fin c) ℂ)
    (P : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin c) (Fin c) ℂ :=
  Zᴴ * (1 - P) * Z

/-- Rectangular trace identity; r and c are independent, including zero. -/
lemma trace_gram (Z : Matrix (Fin r) (Fin c) ℂ) :
    (Zᴴ * Z).trace = (frobeniusSq Z : ℂ) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_mul',
    frobeniusSq, Complex.ofReal_sum, Complex.ofReal_pow]
  rw [Finset.sum_comm]

lemma complement_adjoint (P : Matrix (Fin r) (Fin r) ℂ)
    (hP : Pᴴ = P) : (1-P)ᴴ = 1-P := by
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP]

lemma complement_idempotent (P : Matrix (Fin r) (Fin r) ℂ)
    (hPP : P * P = P) : (1-P)*(1-P) = 1-P := by
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hPP,
    sub_self, sub_zero]

lemma projected_gram (Z : Matrix (Fin r) (Fin c) ℂ)
    (P : Matrix (Fin r) (Fin r) ℂ) (hP : Pᴴ = P) (hPP : P*P=P) :
    (P*Z)ᴴ*(P*Z) = Zᴴ*P*Z := by
  rw [Matrix.conjTranspose_mul, hP]
  calc
    (Zᴴ*P)*(P*Z) = Zᴴ*(P*P)*Z := by simp only [Matrix.mul_assoc]
    _ = Zᴴ*P*Z := by rw [hPP]

/-- The loss is itself an actual Gram matrix, proving its PSD sign. -/
lemma loss_eq_complement_gram (Z : Matrix (Fin r) (Fin c) ℂ)
    (P : Matrix (Fin r) (Fin r) ℂ) (hP : Pᴴ=P) (hPP : P*P=P) :
    gramLoss Z P = ((1-P)*Z)ᴴ*((1-P)*Z) := by
  symm
  exact projected_gram Z (1-P) (complement_adjoint P hP)
    (complement_idempotent P hPP)

lemma loss_posSemidef (Z : Matrix (Fin r) (Fin c) ℂ)
    (P : Matrix (Fin r) (Fin r) ℂ) (hP : Pᴴ=P) (hPP : P*P=P) :
    (gramLoss Z P).PosSemidef := by
  rw [loss_eq_complement_gram Z P hP hPP]
  exact Matrix.posSemidef_conjTranspose_mul_self ((1-P)*Z)

lemma gram_difference (Z : Matrix (Fin r) (Fin c) ℂ)
    (P : Matrix (Fin r) (Fin r) ℂ) (hP : Pᴴ=P) (hPP : P*P=P) :
    Zᴴ*Z - (P*Z)ᴴ*(P*Z) = gramLoss Z P := by
  rw [projected_gram Z P hP hPP]
  simp only [gramLoss, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul]

lemma trace_loss (Z : Matrix (Fin r) (Fin c) ℂ)
    (P : Matrix (Fin r) (Fin r) ℂ) (hP : Pᴴ=P) (hPP : P*P=P) :
    (gramLoss Z P).trace = (frobeniusSq ((1-P)*Z) : ℂ) := by
  rw [loss_eq_complement_gram Z P hP hPP, trace_gram]

lemma trace_loss_difference (Z : Matrix (Fin r) (Fin c) ℂ)
    (P : Matrix (Fin r) (Fin r) ℂ) (hP : Pᴴ=P) (hPP : P*P=P) :
    (gramLoss Z P).trace = ((frobeniusSq Z - frobeniusSq (P*Z) : ℝ) : ℂ) := by
  rw [← gram_difference Z P hP hPP, Matrix.trace_sub, trace_gram, trace_gram]
  exact (Complex.ofReal_sub _ _).symm

lemma frobenius_loss (Z : Matrix (Fin r) (Fin c) ℂ)
    (P : Matrix (Fin r) (Fin r) ℂ) (hP : Pᴴ=P) (hPP : P*P=P) :
    frobeniusSq ((1-P)*Z) = frobeniusSq Z - frobeniusSq (P*Z) := by
  have h := (trace_loss Z P hP hPP).symm.trans (trace_loss_difference Z P hP hPP)
  exact_mod_cast h

lemma re_trace_loss (Z : Matrix (Fin r) (Fin c) ℂ)
    (P : Matrix (Fin r) (Fin r) ℂ) (hP : Pᴴ=P) (hPP : P*P=P) :
    (gramLoss Z P).trace.re = frobeniusSq ((1-P)*Z) := by
  rw [trace_loss Z P hP hPP, Complex.ofReal_re]

end RectangularGramLossCandidate
