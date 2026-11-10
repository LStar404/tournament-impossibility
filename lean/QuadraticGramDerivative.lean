import PolynomialLogDetCandidate
import RealBilinearTrace
import PositiveGramLogDetCandidate
set_option autoImplicit false
noncomputable section
namespace QuadraticGramDerivative
open Matrix Polynomial PolynomialLogDetCandidate
open scoped Matrix.Norms.L2Operator BigOperators
variable {r c : ℕ}
def line (U D : Matrix (Fin r) (Fin c) ℝ) (t : ℝ) := U+t • D
def gramPolynomial (U D : Matrix (Fin r) (Fin c) ℝ) : Matrix (Fin c) (Fin c) ℝ[X] :=
  fun i j => C ((1 : Matrix (Fin c) (Fin c) ℝ) i j) -
    ∑ k, (C (U k i)+X*C (D k i))*(C (U k j)+X*C (D k j))
lemma gram_eval (U D : Matrix (Fin r) (Fin c) ℝ) (t : ℝ) :
    evalMatrix (gramPolynomial U D) t = 1-(line U D t)ᵀ*line U D t := by
  ext i j
  simp [evalMatrix, gramPolynomial, Polynomial.coe_evalRingHom, line,
    Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.add_apply, Matrix.smul_apply]
  rw [Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
  apply Finset.sum_congr rfl
  intro k hk
  ring
lemma gram_derivative_eval (U D : Matrix (Fin r) (Fin c) ℝ) (t : ℝ) :
    evalMatrix (derivativeMatrix (gramPolynomial U D)) t =
      -(Dᵀ*line U D t+(line U D t)ᵀ*D) := by
  ext i j
  simp [evalMatrix, derivativeMatrix, gramPolynomial, Polynomial.coe_evalRingHom,
    Polynomial.derivative_mul, line,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.neg_apply, ← Finset.sum_add_distrib]
  rw [Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
  apply Finset.sum_congr rfl
  intro k hk
  ring
/-- True derivative of the actual quadratic Gram determinant logarithm. -/
theorem logdet_hasDerivAt (U D : Matrix (Fin r) (Fin c) ℝ) (t : ℝ)
    (hn : (1-(line U D t)ᵀ*line U D t).det ≠ 0) :
    HasDerivAt (fun s : ℝ => Real.log (1-(line U D s)ᵀ*line U D s).det)
      (((1-(line U D t)ᵀ*line U D t)⁻¹ *
        (-(Dᵀ*line U D t+(line U D t)ᵀ*D))).trace) t := by
  have hh : (evalMatrix (gramPolynomial U D) t).det ≠ 0 := by rw [gram_eval]; exact hn
  have h := polynomial_log_det_hasDerivAt (gramPolynomial U D) t hh
  simpa only [gram_eval, gram_derivative_eval] using h
end QuadraticGramDerivative
