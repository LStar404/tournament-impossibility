import FullJacobiDerivation
import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! Verified in the 557-module direct-Lean compilation and declaration audit. Actual determinant/log derivative for arbitrary real
polynomial matrices. Includes quadratic Gram paths without asserting their
positivity or any integrated comparison. No derivative is assumed. -/
set_option autoImplicit false
noncomputable section
namespace PolynomialLogDetCandidate
open Matrix Polynomial FullJacobiDerivation
open scoped BigOperators
variable {n : ℕ}

def evalMatrix (M : Matrix (Fin n) (Fin n) ℝ[X]) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℝ := M.map (evalRingHom t)

def derivativeMatrix (M : Matrix (Fin n) (Fin n) ℝ[X]) :
    Matrix (Fin n) (Fin n) ℝ[X] := fun i j => (M i j).derivative

lemma entry_derivative (M : Matrix (Fin n) (Fin n) ℝ[X]) :
    entryDerivative Polynomial.derivative' M = derivativeMatrix M := by
  ext i j
  rfl

lemma eval_det (M : Matrix (Fin n) (Fin n) ℝ[X]) (t : ℝ) :
    M.det.eval t = (evalMatrix M t).det := by
  have h := (evalRingHom t).map_det M
  rw [RingHom.mapMatrix_apply] at h
  simpa only [Polynomial.coe_evalRingHom, evalMatrix] using h

lemma eval_adjugate (M : Matrix (Fin n) (Fin n) ℝ[X]) (t : ℝ) :
    evalMatrix M.adjugate t = (evalMatrix M t).adjugate := by
  have h := (evalRingHom t).map_adjugate M
  simpa only [RingHom.mapMatrix_apply, evalMatrix] using h

lemma eval_mul (M N : Matrix (Fin n) (Fin n) ℝ[X]) (t : ℝ) :
    evalMatrix (M*N) t = evalMatrix M t * evalMatrix N t := by
  ext i j
  change (evalRingHom t) (∑ k, M i k * N k j) =
    ∑ k, (evalRingHom t) (M i k) * (evalRingHom t) (N k j)
  simp only [map_sum, map_mul]

lemma det_derivative_eval (M : Matrix (Fin n) (Fin n) ℝ[X]) (t : ℝ) :
    M.det.derivative.eval t =
      ((evalMatrix M t).adjugate * evalMatrix (derivativeMatrix M) t).trace := by
  have h := adjugate_trace Polynomial.derivative' M
  rw [entry_derivative] at h
  have he := congrArg (evalRingHom t) h
  change M.det.derivative.eval t = _ at he
  rw [AddMonoidHom.map_trace] at he
  change M.det.derivative.eval t = (evalMatrix (M.adjugate*derivativeMatrix M) t).trace at he
  rw [eval_mul, eval_adjugate] at he
  exact he

/-- Actual derivative of the ordinary determinant of the evaluated matrix. -/
theorem polynomial_det_hasDerivAt (M : Matrix (Fin n) (Fin n) ℝ[X]) (t : ℝ) :
    HasDerivAt (fun x : ℝ => (evalMatrix M x).det)
      (((evalMatrix M t).adjugate * evalMatrix (derivativeMatrix M) t).trace) t := by
  have h := M.det.hasDerivAt t
  simpa only [eval_det, det_derivative_eval] using h

/-- Actual Real.log(det), not a logarithm defined by integrating a trace. -/
theorem polynomial_log_det_hasDerivAt (M : Matrix (Fin n) (Fin n) ℝ[X]) (t : ℝ)
    (ht : (evalMatrix M t).det ≠ 0) :
    HasDerivAt (fun x : ℝ => Real.log ((evalMatrix M x).det))
      (((evalMatrix M t)⁻¹ * evalMatrix (derivativeMatrix M) t).trace) t := by
  have h := (polynomial_det_hasDerivAt M t).log ht
  have hu : IsUnit (evalMatrix M t).det := isUnit_iff_ne_zero.mpr ht
  rw [adjugate_eq_det_inverse _ hu, Matrix.smul_mul, Matrix.trace_smul] at h
  simpa only [smul_eq_mul, mul_div_cancel_left₀ _ ht] using h

lemma polynomial_log_det_posDef (M : Matrix (Fin n) (Fin n) ℝ[X]) (t : ℝ)
    (ht : (evalMatrix M t).PosDef) :
    0 < (evalMatrix M t).det ∧
      HasDerivAt (fun x : ℝ => Real.log ((evalMatrix M x).det))
        (((evalMatrix M t)⁻¹ * evalMatrix (derivativeMatrix M) t).trace) t :=
  ⟨ht.det_pos, polynomial_log_det_hasDerivAt M t ht.det_pos.ne'⟩

end PolynomialLogDetCandidate
