import MixedWardUnit

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.typeDecidableEq
namespace MixedWardSolution
open ActualMixedSourceWard ActualMixedWardMatrix MixedWardUnit
variable {I S : Type*} [Fintype I] [Field S] [CharZero S]

def response (K A : I → I → S) (h : I → S) : I → PowerSeries S :=
  (block K A)⁻¹.mulVec (fun i => ∑ j, PowerSeries.C (K i j) * PowerSeries.C (h j))

def covariance (K A : I → I → S) : Matrix I I (PowerSeries S) :=
  (block K A)⁻¹ * Matrix.of (fun i j => PowerSeries.C (K i j))

theorem G_solution (K : I → I → S) (hs : ∀ i j, K i j = K j i)
    (h : I → S) (A : I → I → S) (hA : ∀ i j, A i j = A j i) (i : I) :
    G K hs h A i = PowerSeries.X * response K A h i * Z K hs h A := by
  have hg := funext (first_system K hs h A hA)
  have hx := congrArg (fun v => (block K A)⁻¹.mulVec v) hg
  rw [Matrix.mulVec_mulVec, left_inverse, Matrix.one_mulVec] at hx
  rw [congrFun hx i]
  simp only [response, Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem H_solution (K : I → I → S) (hs : ∀ i j, K i j = K j i)
    (h : I → S) (A : I → I → S) (hA : ∀ i j, A i j = A j i) (i j : I) :
    H K hs h A i j = covariance K A i j * Z K hs h A +
      PowerSeries.X^2 * response K A h i * response K A h j * Z K hs h A := by
  suffices ht : H K hs h A i j = covariance K A i j * Z K hs h A +
      PowerSeries.X * response K A h i * G K hs h A j by
    rw [ht, G_solution K hs h A hA j]
    ring
  have hg := funext (fun i => second_system K hs h A hA i j)
  have hx := congrArg (fun v => (block K A)⁻¹.mulVec v) hg
  rw [Matrix.mulVec_mulVec, left_inverse, Matrix.one_mulVec] at hx
  rw [congrFun hx i]
  simp only [covariance, response, Matrix.mulVec, Matrix.mul_apply, Matrix.of_apply,
    dotProduct, mul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro k _
    ring
  · apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring

end MixedWardSolution
#print axioms MixedWardSolution.G_solution
#print axioms MixedWardSolution.H_solution
