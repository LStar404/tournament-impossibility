import ActualMixedSourceWard
import Mathlib.LinearAlgebra.Matrix.SchurComplement

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.typeDecidableEq
namespace ActualMixedWardMatrix
open ActualMixedSourceWard
variable {I S : Type*} [Fintype I] [Field S] [CharZero S]

def block (K A : I → I → S) : Matrix I I (PowerSeries S) :=
  1 + (PowerSeries.X : PowerSeries S)^2 •
    (Matrix.of (fun i j => PowerSeries.C (K i j)) * Matrix.of (fun i j => PowerSeries.C (A i j)))

theorem block_mulVec (K A : I → I → S) (f : I → PowerSeries S) (i : I) :
    (block K A).mulVec f i = f i + PowerSeries.X^2 *
      ∑ k, PowerSeries.C (K i k) * ∑ j, PowerSeries.C (A k j) * f j := by
  rw [block, Matrix.add_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec]
  rw [Matrix.one_mulVec]
  rfl

theorem first_system (K : I → I → S) (hs : ∀ i j, K i j = K j i)
    (h : I → S) (A : I → I → S) (hA : ∀ i j, A i j = A j i) (i : I) :
    (block K A).mulVec (G K hs h A) i =
      PowerSeries.X * (∑ k, PowerSeries.C (K i k) * PowerSeries.C (h k)) * Z K hs h A := by
  rw [block_mulVec, first_ward K hs h A hA]
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]
  have he (k : I) :
      PowerSeries.C (K i k) * (PowerSeries.X * (PowerSeries.C (h k) * Z K hs h A)) =
      PowerSeries.X * (PowerSeries.C (K i k) * PowerSeries.C (h k)) * Z K hs h A := by ring
  simp only [he]
  have hf (k : I) :
      PowerSeries.C (K i k) * (PowerSeries.X^2 * ∑ j, PowerSeries.C (A k j) * G K hs h A j) =
      PowerSeries.X^2 * (PowerSeries.C (K i k) * ∑ j, PowerSeries.C (A k j) * G K hs h A j) := by ring
  simp only [Finset.mul_sum] at hf
  simp only [hf]
  ring

theorem H_symm (K : I → I → S) (hs : ∀ i j, K i j = K j i)
    (h : I → S) (A : I → I → S) (i j : I) : H K hs h A i j = H K hs h A j i := by
  unfold H
  rw [mul_comm]

theorem second_system (K : I → I → S) (hs : ∀ i j, K i j = K j i)
    (h : I → S) (A : I → I → S) (hA : ∀ i j, A i j = A j i) (i j : I) :
    (block K A).mulVec (fun l => H K hs h A l j) i =
      PowerSeries.C (K i j) * Z K hs h A +
      PowerSeries.X * (∑ k, PowerSeries.C (K i k) * PowerSeries.C (h k)) * G K hs h A j := by
  rw [block_mulVec, second_ward K hs h A hA]
  have hsym (l : I) : H K hs h A j l = H K hs h A l j := H_symm K hs h A j l
  simp only [hsym, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]
  have he (k : I) :
      PowerSeries.C (K i k) * (PowerSeries.X * (PowerSeries.C (h k) * G K hs h A j)) =
      PowerSeries.X * (PowerSeries.C (K i k) * PowerSeries.C (h k)) * G K hs h A j := by ring
  simp only [he]
  have hf (k : I) :
      PowerSeries.C (K i k) * (PowerSeries.X^2 * ∑ l, PowerSeries.C (A k l) * H K hs h A l j) =
      PowerSeries.X^2 * (PowerSeries.C (K i k) * ∑ l, PowerSeries.C (A k l) * H K hs h A l j) := by ring
  simp only [Finset.mul_sum] at hf
  simp only [hf]
  ring

end ActualMixedWardMatrix
#print axioms ActualMixedWardMatrix.first_system

#print axioms ActualMixedWardMatrix.second_system
