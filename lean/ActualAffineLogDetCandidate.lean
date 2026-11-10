import FullJacobiDerivation
import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! Verified in the 557-module direct-Lean compilation and declaration audit. Real analytic derivative of an actual affine determinant.
The determinant is the ordinary Matrix.det, not an integral-defined proxy.
No projection-path positivity or endpoint comparison is claimed here. -/
set_option autoImplicit false
noncomputable section
namespace ActualAffineLogDetCandidate
open Matrix Polynomial FullJacobiDerivation
open scoped BigOperators
variable {n : ℕ}

def affinePolynomial (A B : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ[X] :=
  fun i j => C (A i j) + X * C (B i j)

lemma affine_eval (A B : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    (affinePolynomial A B).map (evalRingHom t) = A+t • B := by
  ext i j
  simp [affinePolynomial, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply]
  ring

lemma determinant_eval (A B : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    ((affinePolynomial A B).det).eval t = (A+t • B).det := by
  have h := (evalRingHom t).map_det (affinePolynomial A B)
  rw [RingHom.mapMatrix_apply, affine_eval] at h
  simpa only [Polynomial.coe_evalRingHom] using h

lemma derivative_matrix (A B : Matrix (Fin n) (Fin n) ℝ) :
    entryDerivative Polynomial.derivative' (affinePolynomial A B) = B.map C := by
  ext i j
  simp [entryDerivative, affinePolynomial, Polynomial.derivative']

lemma determinant_derivative_eval (A B : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    ((affinePolynomial A B).det).derivative.eval t =
      ((A+t • B).adjugate * B).trace := by
  have h := adjugate_trace Polynomial.derivative' (affinePolynomial A B)
  rw [derivative_matrix] at h
  have he := congrArg (evalRingHom t) h
  have ha : ((affinePolynomial A B).adjugate).map (evalRingHom t) =
      (A+t • B).adjugate := by
    have hmap := (evalRingHom t).map_adjugate (affinePolynomial A B)
    simp only [RingHom.mapMatrix_apply] at hmap
    rw [affine_eval] at hmap
    exact hmap
  change ((affinePolynomial A B).det).derivative.eval t = _ at he
  rw [AddMonoidHom.map_trace] at he
  have hm : (((affinePolynomial A B).adjugate * B.map C).map (evalRingHom t)) =
      (A+t • B).adjugate * B := by
    ext i j
    change (evalRingHom t) (∑ k, (affinePolynomial A B).adjugate i k * C (B k j)) = _
    simp only [map_sum, map_mul]
    have hae (i k : Fin n) : (evalRingHom t) ((affinePolynomial A B).adjugate i k) =
        (A+t • B).adjugate i k := congrFun (congrFun ha i) k
    simp only [hae, Polynomial.coe_evalRingHom, Polynomial.eval_C, Matrix.mul_apply]
  rw [hm] at he
  exact he

/-- Actual determinant derivative, proved via the actual determinant polynomial. -/
theorem hasDerivAt_det_affine (A B : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => (A+x • B).det)
      (((A+t • B).adjugate * B).trace) t := by
  have h := ((affinePolynomial A B).det).hasDerivAt t
  simpa only [determinant_eval, determinant_derivative_eval] using h

/-- No derivative is a premise; only pointwise nonsingularity remains explicit. -/
theorem hasDerivAt_log_det_affine (A B : Matrix (Fin n) (Fin n) ℝ) (t : ℝ)
    (ht : (A+t • B).det ≠ 0) :
    HasDerivAt (fun x : ℝ => Real.log ((A+x • B).det))
      (((A+t • B)⁻¹ * B).trace) t := by
  have h := (hasDerivAt_det_affine A B t).log ht
  have hu : IsUnit (A+t • B).det := isUnit_iff_ne_zero.mpr ht
  rw [adjugate_eq_det_inverse _ hu, Matrix.smul_mul, Matrix.trace_smul] at h
  simpa only [smul_eq_mul, mul_div_cancel_left₀ _ ht] using h

/-- Positive definite real matrices supply the required determinant sign. -/
theorem hasDerivAt_log_det_affine_posDef (A B : Matrix (Fin n) (Fin n) ℝ)
    (t : ℝ) (ht : (A+t • B).PosDef) :
    0 < (A+t • B).det ∧
    HasDerivAt (fun x : ℝ => Real.log ((A+x • B).det))
      (((A+t • B)⁻¹ * B).trace) t :=
  ⟨ht.det_pos, hasDerivAt_log_det_affine A B t ht.det_pos.ne'⟩

end ActualAffineLogDetCandidate
