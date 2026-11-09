import MixedCovarianceDerivative

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.typeDecidableEq
namespace MixedSourceQuadraticDerivative
open Matrix ActualMixedWardMatrix MixedWardSolution MixedCovarianceSymmetry MixedCovarianceDerivative
open FullJacobiDerivation
variable {I S : Type*} [Fintype I] [Field S] [CharZero S]

def source (K A : I → I → S) (h : I → S) : PowerSeries S :=
  PowerSeries.C (1/2:S) * PowerSeries.X^2 *
    ((fun i => PowerSeries.C (h i)) ⬝ᵥ (covariance K A).mulVec (fun i => PowerSeries.C (h i)))

theorem response_eq (K A : I → I → S) (h : I → S) :
    response K A h = (covariance K A).mulVec (fun i => PowerSeries.C (h i)) := by
  change (block K A)⁻¹.mulVec ((constantMatrix K).mulVec _) = _
  rw [Matrix.mulVec_mulVec]
  rfl

theorem constant_bilinear_derivative (M : Matrix I I (PowerSeries S)) (h : I → S) :
    PowerSeries.derivative ((fun i => PowerSeries.C (h i)) ⬝ᵥ M.mulVec (fun i => PowerSeries.C (h i))) =
    (fun i => PowerSeries.C (h i)) ⬝ᵥ (entryDerivative PowerSeries.derivative M).mulVec (fun i => PowerSeries.C (h i)) := by
  simp [dotProduct, Matrix.mulVec, entryDerivative, Derivation.leibniz, Finset.mul_sum, mul_comm]

theorem quadratic_contraction (K A : I → I → S) (h : I → S)
    (hK : ∀ i j, K i j = K j i) (hA : ∀ i j, A i j = A j i) :
    (fun i => PowerSeries.C (h i)) ⬝ᵥ
      (covariance K A * constantMatrix A * covariance K A).mulVec (fun i => PowerSeries.C (h i)) =
    response K A h ⬝ᵥ (constantMatrix A).mulVec (response K A h) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  nth_rw 1 [← covariance_transpose K A hK hA]
  rw [Matrix.dotProduct_transpose_mulVec, dotProduct_comm, ← response_eq]

theorem source_constant (K A : I → I → S) (h : I → S) :
    (source K A h).constantCoeff = 0 := by simp [source]

theorem source_derivative (K A : I → I → S) (h : I → S)
    (hK : ∀ i j, K i j = K j i) (hA : ∀ i j, A i j = A j i) :
    PowerSeries.derivative (source K A h) =
      PowerSeries.X * ((fun i => PowerSeries.C (h i)) ⬝ᵥ response K A h) -
      PowerSeries.X^3 * (response K A h ⬝ᵥ (constantMatrix A).mulVec (response K A h)) := by
  rw [source, Derivation.leibniz, constant_bilinear_derivative, covariance_derivative]
  rw [Matrix.smul_mulVec, dotProduct_smul, quadratic_contraction K A h hK hA]
  simp only [Derivation.leibniz, PowerSeries.derivative_C, PowerSeries.derivative_pow,
    PowerSeries.derivative_X, smul_eq_mul]
  rw [← response_eq]
  have hh : PowerSeries.C (1/2:S) * 2 = (1:PowerSeries S) := by
    rw [show (2:PowerSeries S) = PowerSeries.C (2:S) from (map_natCast _ 2).symm, ← map_mul]
    norm_num
  linear_combination (PowerSeries.X * ((fun i => PowerSeries.C (h i)) ⬝ᵥ response K A h) -
    PowerSeries.X^3 * (response K A h ⬝ᵥ (constantMatrix A).mulVec (response K A h))) * hh

end MixedSourceQuadraticDerivative
#print axioms MixedSourceQuadraticDerivative.source_derivative
