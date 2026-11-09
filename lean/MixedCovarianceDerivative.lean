import MixedCovarianceSymmetry
import MatrixDerivationInverse

noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace MixedCovarianceDerivative
open Matrix ActualMixedWardMatrix MixedWardUnit MixedWardSolution MixedCovarianceSymmetry
open FullJacobiDerivation MatrixDerivationInverse
variable {I S : Type*} [Fintype I] [Field S] [CharZero S]

theorem constant_derivative (K : I → I → S) :
    entryDerivative PowerSeries.derivative (constantMatrix K) = 0 := by
  apply Matrix.ext
  intro i j
  simp [entryDerivative, constantMatrix]

theorem block_derivative (K A : I → I → S) :
    entryDerivative PowerSeries.derivative (block K A) =
      (2*(PowerSeries.X : PowerSeries S)) • (constantMatrix K * constantMatrix A) := by
  apply Matrix.ext
  intro i j
  simp [entryDerivative, block, constantMatrix, Matrix.add_apply, Matrix.smul_apply,
    Matrix.mul_apply, Matrix.one_apply, apply_ite, Derivation.leibniz, PowerSeries.derivative_pow]
  ring

theorem covariance_derivative (K A : I → I → S) :
    entryDerivative PowerSeries.derivative (covariance K A) =
      -(2*(PowerSeries.X : PowerSeries S)) • (covariance K A * constantMatrix A * covariance K A) := by
  change entryDerivative PowerSeries.derivative ((block K A)⁻¹ * constantMatrix K) = _
  rw [derivative_mul, constant_derivative, Matrix.mul_zero, add_zero,
    inverse_derivative _ _ (det_isUnit K A), block_derivative]
  change -((block K A)⁻¹ * ((2*(PowerSeries.X : PowerSeries S)) • (constantMatrix K * constantMatrix A)) * (block K A)⁻¹) * constantMatrix K = _
  simp only [covariance, constantMatrix, Matrix.mul_smul, Matrix.smul_mul, neg_mul,
    neg_smul, Matrix.mul_assoc]

end MixedCovarianceDerivative
#print axioms MixedCovarianceDerivative.covariance_derivative
