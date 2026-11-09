import PhysicalLowMoments

noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace PhysicalCovarianceInitial
open Matrix PhysicalTiltedCovariance MixedCovarianceSymmetry
variable {I S : Type*} [Fintype I] [Field S] [CharZero S]

theorem inverse_constant (K A : I → I → S) :
    ((MixedEvenMatrix.block K A)⁻¹).map PowerSeries.constantCoeff=1 := by
  have hh := congrArg (fun M : Matrix I I (PowerSeries S) => M.map PowerSeries.constantCoeff)
    (Matrix.mul_nonsing_inv (MixedEvenMatrix.block K A) (MixedEvenMatrix.det_isUnit K A))
  rw [Matrix.map_mul,MixedEvenMatrix.constant_block,Matrix.one_mul,
    Matrix.map_one _ (map_zero _) (map_one _)] at hh
  exact hh

theorem covariance_first (K A : I → I → S) (i j : I) :
    (covariance K A i j).coeff 1=K i j := by
  have hh (i j : I) := congrArg (fun M : Matrix I I S => M i j) (inverse_constant K A)
  simp only [Matrix.map_apply] at hh
  simp [covariance,Matrix.smul_apply,PowerSeries.coeff_succ_X_mul,Matrix.mul_apply,
    constantMatrix,hh,Matrix.one_apply]

theorem third_second_zero (K A : I → I → S) (h : I → S) (i : I) (hi : K i i=0) :
    (PhysicalWordEvenDescent.moment K A h [i,i,i]).coeff 2=0 := by
  rw [PhysicalLowMoments.third]
  norm_num [pow_succ,PowerSeries.coeff_mul,Finset.Nat.antidiagonal_succ,
    mean_constant,covariance_constant,covariance_first,hi]

theorem fourth_second_zero (K A : I → I → S) (h : I → S) (i : I) (hi : K i i=0) :
    (PhysicalWordEvenDescent.moment K A h [i,i,i,i]).coeff 2=0 := by
  rw [PhysicalLowMoments.fourth]
  norm_num [pow_succ,PowerSeries.coeff_mul,Finset.Nat.antidiagonal_succ,
    mean_constant,covariance_constant,covariance_first,hi]

end PhysicalCovarianceInitial
#print axioms PhysicalCovarianceInitial.fourth_second_zero
