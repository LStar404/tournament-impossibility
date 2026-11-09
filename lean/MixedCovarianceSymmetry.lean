import MixedWardSolution

noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace MixedCovarianceSymmetry
open Matrix ActualMixedWardMatrix MixedWardUnit MixedWardSolution
variable {I S : Type*} [Fintype I] [Field S] [CharZero S]

def constantMatrix (K : I → I → S) : Matrix I I (PowerSeries S) :=
  Matrix.of (fun i j => PowerSeries.C (K i j))

theorem constant_transpose (K : I → I → S) (hs : ∀ i j, K i j = K j i) :
    (constantMatrix K)ᵀ = constantMatrix K := by
  apply Matrix.ext
  intro i j
  exact congrArg PowerSeries.C (hs j i)

theorem intertwine (K A : I → I → S)
    (hK : ∀ i j, K i j = K j i) (hA : ∀ i j, A i j = A j i) :
    block K A * constantMatrix K = constantMatrix K * (block K A)ᵀ := by
  change (1 + (PowerSeries.X : PowerSeries S)^2 • (constantMatrix K * constantMatrix A)) * constantMatrix K =
    constantMatrix K * (1 + (PowerSeries.X : PowerSeries S)^2 • (constantMatrix K * constantMatrix A))ᵀ
  rw [transpose_add, transpose_one, transpose_smul, transpose_mul,
    constant_transpose A hA, constant_transpose K hK]
  simp only [add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]

theorem covariance_transpose (K A : I → I → S)
    (hK : ∀ i j, K i j = K j i) (hA : ∀ i j, A i j = A j i) :
    (covariance K A)ᵀ = covariance K A := by
  change ((block K A)⁻¹ * constantMatrix K)ᵀ = (block K A)⁻¹ * constantMatrix K
  rw [transpose_mul, constant_transpose K hK]
  have ht : (block K A)ᵀ * ((block K A)⁻¹)ᵀ = 1 := by
    rw [← transpose_mul, left_inverse, transpose_one]
  have he := intertwine K A hK hA
  calc
    constantMatrix K * ((block K A)⁻¹)ᵀ =
        (block K A)⁻¹ * (block K A * constantMatrix K) * ((block K A)⁻¹)ᵀ := by
      rw [← Matrix.mul_assoc, left_inverse, one_mul]
    _ = (block K A)⁻¹ * (constantMatrix K * (block K A)ᵀ) * ((block K A)⁻¹)ᵀ := by rw [he]
    _ = _ := by rw [Matrix.mul_assoc, Matrix.mul_assoc, ht, mul_one]

theorem covariance_symm (K A : I → I → S)
    (hK : ∀ i j, K i j = K j i) (hA : ∀ i j, A i j = A j i) (i j : I) :
    covariance K A i j = covariance K A j i := by
  have hh := congrArg (fun M : Matrix I I (PowerSeries S) => M j i) (covariance_transpose K A hK hA)
  exact hh

end MixedCovarianceSymmetry
#print axioms MixedCovarianceSymmetry.covariance_symm
