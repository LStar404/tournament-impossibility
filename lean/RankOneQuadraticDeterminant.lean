import RankOneQuadraticUnitBranch
import Mathlib.LinearAlgebra.Matrix.SchurComplement

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.typeDecidableEq
namespace RankOneQuadraticDeterminant
open Matrix RankOneQuadraticCoefficients RankOneQuadraticODE LinearSourcePairingFactor
variable {L R : Type*} [Fintype L] [CommRing R]

def rankOne (a : R) (h : L → R) : Matrix L L R := fun i j => a * h i * h j

theorem rankOne_polynomial (a : R) (h : L → R) :
    (∑ i, ∑ j, (rankOne a h i j) • (MvPolynomial.X i * MvPolynomial.X j)) =
      a • (LinearSourceExpansion.source h)^2 := by
  simp only [LinearSourceExpansion.source, pow_two, Finset.sum_mul, Finset.mul_sum,
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp [rankOne, smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc, mul_comm, mul_left_comm]

theorem det_rankOne (C : Matrix L L R) (h : L → R) (a t : R) :
    (1 + t • (C * rankOne a h)).det = 1 + t * a * quadratic C h := by
  let u : L → R := fun i => t * a * ∑ j, C i j * h j
  have he : t • (C * rankOne a h) = replicateCol Unit u * replicateRow Unit h := by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, rankOne,
      replicateCol_apply, replicateRow_apply, Fintype.sum_unique, u]
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he, det_one_add_replicateCol_mul_replicateRow]
  congr 1
  simp only [dotProduct, u, quadratic, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

variable {S : Type*} [Field S] [CharZero S]

def block (C : Matrix L L S) (h : L → S) (a : S) : Matrix L L (PowerSeries S) :=
  1 + (PowerSeries.X : PowerSeries S) •
    ((Matrix.of (fun i j => PowerSeries.C (C i j))) * rankOne (PowerSeries.C a) (fun i => PowerSeries.C (h i)))

theorem block_det (C : Matrix L L S) (h : L → S) (a : S) :
    (block C h a).det = denominator (a * quadratic C h) := by
  rw [block, det_rankOne]
  have hq : quadratic (Matrix.of (fun i j => (PowerSeries.C (C i j) : PowerSeries S))) (fun i => PowerSeries.C (h i)) =
      PowerSeries.C (quadratic C h) := by
    simp only [quadratic, Matrix.of_apply, map_sum, map_mul]
  rw [hq]
  simp only [denominator, map_mul]
  ring

theorem actual_wick_det_identity (C : Matrix L L S) (hs : ∀ i j, C i j = C j i)
    (h : L → S) (a : S) : (series C hs h a)^2 * (block C h a).det = 1 := by
  rw [block_det]
  exact RankOneQuadraticUnitBranch.square_identity C hs h a

end RankOneQuadraticDeterminant
#print axioms RankOneQuadraticDeterminant.det_rankOne
#print axioms RankOneQuadraticDeterminant.actual_wick_det_identity
