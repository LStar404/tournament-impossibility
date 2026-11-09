import MixedEvenMatrix
import PolynomialTiltedRecurrence

noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace PhysicalTiltedCovariance
open Matrix MixedCovarianceSymmetry
variable {I S : Type*} [Fintype I] [Field S] [CharZero S]

def covariance (K A : I → I → S) : Matrix I I (PowerSeries S) :=
  (PowerSeries.X : PowerSeries S) • ((MixedEvenMatrix.block K A)⁻¹ * constantMatrix K)

def mean (K A : I → I → S) (h : I → S) : I → PowerSeries S :=
  (covariance K A).mulVec (fun i => PowerSeries.C (h i))

theorem expand_covariance (K A : I → I → S) (i j : I) :
    PowerSeries.expand 2 (by decide) (covariance K A i j) =
      PowerSeries.X^2 * MixedWardSolution.covariance K A i j := by
  have he (a b : I) := congrArg (fun M => M a b) (MixedEvenMatrix.expand_inverse K A)
  simp only [Matrix.map_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at he
  simp [covariance, Matrix.smul_apply, Matrix.mul_apply, constantMatrix,
    PowerSeries.expand_C, he, MixedWardSolution.covariance, Finset.mul_sum]

theorem expand_mean (K A : I → I → S) (h : I → S) (i : I) :
    PowerSeries.expand 2 (by decide) (mean K A h i) =
      PowerSeries.X^2 * MixedWardSolution.response K A h i := by
  simp only [mean, Matrix.mulVec, dotProduct, map_sum, map_mul, expand_covariance,
    PowerSeries.expand_C, MixedWardSolution.response, MixedWardSolution.covariance,
    Matrix.mul_apply, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  ring

theorem covariance_constant (K A : I → I → S) (i j : I) :
    (covariance K A i j).constantCoeff = 0 := by simp [covariance,Matrix.smul_apply]

theorem mean_constant (K A : I → I → S) (h : I → S) (i : I) :
    (mean K A h i).constantCoeff = 0 := by
  simp [mean, Matrix.mulVec, dotProduct, covariance_constant]

/-- The raw covariance convention, with the true inverse on the right. -/
theorem raw_covariance (K : I → I → S) :
    covariance K (1 : Matrix I I S) =
      (PowerSeries.X : PowerSeries S) • (constantMatrix K * (1 + (PowerSeries.X : PowerSeries S) • constantMatrix K)⁻¹) := by
  have hc : constantMatrix (1 : Matrix I I S) = 1 := by
    apply Matrix.ext; intro i j; simp [constantMatrix,Matrix.one_apply,apply_ite]
  have hb : MixedEvenMatrix.block K (1 : Matrix I I S) =
      1 + (PowerSeries.X : PowerSeries S) • constantMatrix K := by simp [MixedEvenMatrix.block,hc]
  have hu := MixedEvenMatrix.det_isUnit K (1 : Matrix I I S)
  have hl := Matrix.nonsing_inv_mul _ hu
  have hr := Matrix.mul_nonsing_inv _ hu
  have comm : MixedEvenMatrix.block K (1 : Matrix I I S) * constantMatrix K =
      constantMatrix K * MixedEvenMatrix.block K (1 : Matrix I I S) := by
    rw [hb]; simp only [add_mul,mul_add,one_mul,mul_one,Matrix.smul_mul,Matrix.mul_smul]
  have hi := congrArg (fun M => (MixedEvenMatrix.block K (1 : Matrix I I S))⁻¹ * M *
      (MixedEvenMatrix.block K (1 : Matrix I I S))⁻¹) comm
  simp only [← Matrix.mul_assoc,hl,one_mul] at hi
  have hh : (MixedEvenMatrix.block K (1 : Matrix I I S))⁻¹ * constantMatrix K =
      constantMatrix K * (MixedEvenMatrix.block K (1 : Matrix I I S))⁻¹ := by
    rw [Matrix.mul_assoc ((MixedEvenMatrix.block K (1 : Matrix I I S))⁻¹ * constantMatrix K),hr,mul_one] at hi
    exact hi.symm
  unfold covariance
  rw [hh,hb]

/-- The actual raw mean is W times the all-ones vector. -/
theorem raw_mean (K : I → I → S) :
    mean K (1 : Matrix I I S) (fun _ => 1) =
      ((PowerSeries.X : PowerSeries S) •
        (constantMatrix K * (1 + (PowerSeries.X : PowerSeries S) • constantMatrix K)⁻¹)).mulVec
        (fun _ => 1) := by
  unfold mean
  rw [raw_covariance]
  simp only [map_one]

end PhysicalTiltedCovariance
#print axioms PhysicalTiltedCovariance.raw_covariance
#print axioms PhysicalTiltedCovariance.expand_mean
