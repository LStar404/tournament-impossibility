import FullJacobiDerivation

noncomputable section
open scoped BigOperators
namespace MatrixDerivationInverse
open Matrix FullJacobiDerivation
variable {R A I : Type*} [CommRing R] [CommRing A] [Algebra R A] [Fintype I] [DecidableEq I]

theorem derivative_mul (D : Derivation R A A) (M N : Matrix I I A) :
    entryDerivative D (M*N) = entryDerivative D M * N + M * entryDerivative D N := by
  ext i j
  simp only [entryDerivative, Matrix.of_apply, Matrix.mul_apply, map_sum,
    Matrix.add_apply, Derivation.leibniz, smul_eq_mul, Finset.sum_add_distrib]
  simp only [mul_comm, add_comm]

theorem derivative_one (D : Derivation R A A) :
    entryDerivative D (1 : Matrix I I A) = 0 := by
  ext i j
  simp [entryDerivative, Matrix.one_apply, apply_ite]

theorem inverse_derivative (D : Derivation R A A) (M : Matrix I I A) (hM : IsUnit M.det) :
    entryDerivative D M⁻¹ = -(M⁻¹ * entryDerivative D M * M⁻¹) := by
  have he := congrArg (entryDerivative D) (Matrix.mul_nonsing_inv M hM)
  rw [derivative_mul, derivative_one] at he
  have hh := congrArg (fun X => M⁻¹ * X) he
  simp only [Matrix.mul_add, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul M hM,
    Matrix.one_mul, Matrix.mul_zero] at hh
  apply eq_neg_iff_add_eq_zero.mpr
  rw [add_comm]
  exact hh

end MatrixDerivationInverse
#print axioms MatrixDerivationInverse.inverse_derivative
