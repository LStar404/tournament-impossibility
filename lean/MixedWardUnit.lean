import ActualMixedWardMatrix

noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace MixedWardUnit
open ActualMixedWardMatrix
variable {I S : Type*} [Fintype I] [Field S] [CharZero S]

theorem constant_block (K A : I → I → S) :
    (block K A).map PowerSeries.constantCoeff = 1 := by
  ext i j
  simp [block, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, apply_ite]

theorem constant_det (K A : I → I → S) :
    (block K A).det.constantCoeff = 1 := by
  rw [RingHom.map_det]
  change ((block K A).map PowerSeries.constantCoeff).det = 1
  rw [constant_block, Matrix.det_one]

theorem det_isUnit (K A : I → I → S) : IsUnit (block K A).det := by
  rw [PowerSeries.isUnit_iff_constantCoeff, constant_det]
  exact isUnit_one

theorem block_isUnit (K A : I → I → S) : IsUnit (block K A) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr (det_isUnit K A)

theorem right_inverse (K A : I → I → S) : block K A * (block K A)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (det_isUnit K A)

theorem left_inverse (K A : I → I → S) : (block K A)⁻¹ * block K A = 1 :=
  Matrix.nonsing_inv_mul _ (det_isUnit K A)

end MixedWardUnit
#print axioms MixedWardUnit.block_isUnit
#print axioms MixedWardUnit.left_inverse
