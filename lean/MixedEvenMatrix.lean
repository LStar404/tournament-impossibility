import ActualMixedDeterminantFormula

noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace MixedEvenMatrix
open Matrix MixedCovarianceSymmetry
variable {I S : Type*} [Fintype I] [Field S] [CharZero S]

def block (K A : I → I → S) : Matrix I I (PowerSeries S) :=
  1 + (PowerSeries.X : PowerSeries S) • (constantMatrix K * constantMatrix A)

theorem constant_block (K A : I → I → S) :
    (block K A).map PowerSeries.constantCoeff = 1 := by
  apply Matrix.ext; intro i j
  simp [block, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, apply_ite, PowerSeries.expand_C]

theorem constant_det (K A : I → I → S) : (block K A).det.constantCoeff = 1 := by
  rw [RingHom.map_det]
  change ((block K A).map PowerSeries.constantCoeff).det = 1
  rw [constant_block, Matrix.det_one]

theorem det_isUnit (K A : I → I → S) : IsUnit (block K A).det := by
  rw [PowerSeries.isUnit_iff_constantCoeff, constant_det]
  exact isUnit_one

theorem expand_block (K A : I → I → S) :
    (block K A).map (PowerSeries.expand 2 (by decide)).toRingHom = ActualMixedWardMatrix.block K A := by
  apply Matrix.ext; intro i j
  simp [block, ActualMixedWardMatrix.block, constantMatrix, Matrix.mul_apply,
    Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, apply_ite, PowerSeries.expand_C]

theorem expand_inverse (K A : I → I → S) :
    ((block K A)⁻¹).map (PowerSeries.expand 2 (by decide)).toRingHom =
      (ActualMixedWardMatrix.block K A)⁻¹ := by
  have hi := Matrix.mul_nonsing_inv (block K A) (det_isUnit K A)
  have hm := congrArg (fun M => M.map (PowerSeries.expand 2 (by decide)).toRingHom) hi
  rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), expand_block] at hm
  have hh := congrArg (fun M => (ActualMixedWardMatrix.block K A)⁻¹ * M) hm
  simpa only [← Matrix.mul_assoc, MixedWardUnit.left_inverse, Matrix.one_mul, Matrix.mul_one] using hh

end MixedEvenMatrix
#print axioms MixedEvenMatrix.expand_inverse
