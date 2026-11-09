import DerivationDeterminantColumns

noncomputable section
open scoped BigOperators
namespace FullJacobiDerivation
open Matrix
variable {R A I : Type*} [CommRing R] [CommRing A] [Algebra R A] [Fintype I] [DecidableEq I]

def entryDerivative (D : Derivation R A A) (M : Matrix I I A) : Matrix I I A :=
  Matrix.of (fun i j => D (M i j))

theorem adjugate_trace (D : Derivation R A A) (M : Matrix I I A) :
    D M.det = (M.adjugate * entryDerivative D M).trace := by
  rw [DerivationDeterminantColumns.determinant_columns]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, entryDerivative, Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec]
  rfl

theorem adjugate_eq_det_inverse (M : Matrix I I A) (hM : IsUnit M.det) :
    M.adjugate = M.det • M⁻¹ := by
  calc
    M.adjugate = M.adjugate * (M * M⁻¹) := by rw [Matrix.mul_nonsing_inv _ hM, Matrix.mul_one]
    _ = (M.adjugate * M) * M⁻¹ := (Matrix.mul_assoc _ _ _).symm
    _ = _ := by rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]

/-- Full algebraic Jacobi formula, not just a derivative evaluated at zero. -/
theorem unit_jacobi (D : Derivation R A A) (M : Matrix I I A) (hM : IsUnit M.det) :
    D M.det = M.det * (M⁻¹ * entryDerivative D M).trace := by
  rw [adjugate_trace, adjugate_eq_det_inverse M hM, Matrix.smul_mul, Matrix.trace_smul]
  rfl

end FullJacobiDerivation
#print axioms FullJacobiDerivation.adjugate_trace
#print axioms FullJacobiDerivation.unit_jacobi
