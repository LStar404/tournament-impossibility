import EuclideanBilinearContraction
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

noncomputable section
namespace SkewLagrangeBound
open Matrix
variable {I : Type*} [Fintype I]

theorem lagrange (x y : I → ℝ) :
    (∑ i, ∑ j, (y i*x j-y j*x i)^2) =
      2*((∑ i,x i^2)*(∑ i,y i^2)-(∑ i,x i*y i)^2) := by
  have he (i j : I) : (y i*x j-y j*x i)^2 =
      y i^2*x j^2 + x i^2*y j^2 - 2*(x i*y i)*(x j*y j) := by ring
  simp_rw [he,Finset.sum_sub_distrib,Finset.sum_add_distrib,
    ← Finset.mul_sum,← Finset.sum_mul]
  simp_rw [mul_comm (2:ℝ), ← Finset.sum_mul]
  ring

theorem skew_pair (A : Matrix I I ℝ) (hA : ∀ i j,A j i= -A i j)
    (x y : I → ℝ) :
    (∑ i,∑ j,A i j*(y i*x j-y j*x i)) = 2*(∑ i,y i*(A.mulVec x) i) := by
  have hs : (∑ i,∑ j,A i j*y j*x i)= -(∑ i,∑ j,A i j*y i*x j) := by
    rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hA i j]
    ring
  simp_rw [mul_sub,Finset.sum_sub_distrib]
  simp_rw [show ∀ i j,A i j*(y i*x j)=A i j*y i*x j by intros; ring,
    show ∀ i j,A i j*(y j*x i)=A i j*y j*x i by intros; ring]
  rw [hs]
  simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
  have hh : (∑ i,∑ j,A i j*y i*x j)=(∑ i,∑ j,y i*(A i j*x j)) := by
    congr 1; ext i; congr 1; ext j; ring
  rw [hh]
  simp_rw [← Finset.mul_sum]
  ring

theorem bilinear_squared (A : Matrix I I ℝ) (hA : ∀ i j,A j i= -A i j)
    (x y : I → ℝ) :
    2*(∑ i,y i*(A.mulVec x) i)^2 ≤
      (∑ i,∑ j,A i j^2)*((∑ i,x i^2)*(∑ i,y i^2)) := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (I × I))
    (fun p => A p.1 p.2) (fun p => y p.1*x p.2-y p.2*x p.1)
  simp only [Fintype.sum_prod_type] at hc
  rw [skew_pair A hA x y,lagrange] at hc
  have hf : 0 ≤ ∑ i,∑ j,A i j^2 := Finset.sum_nonneg (fun i _ =>
    Finset.sum_nonneg (fun j _ => sq_nonneg _))
  have hp := mul_nonneg hf (sq_nonneg (∑ i,x i*y i))
  nlinarith

theorem vector_squared (A : Matrix I I ℝ) (hA : ∀ i j,A j i= -A i j)
    (x : I → ℝ) :
    2*(∑ i,((A.mulVec x) i)^2) ≤ (∑ i,∑ j,A i j^2)*(∑ i,x i^2) := by
  have hc := bilinear_squared A hA x (A.mulVec x)
  simp only [← sq] at hc
  have hy : 0 ≤ ∑ i,((A.mulVec x) i)^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hf : 0 ≤ (∑ i,∑ j,A i j^2)*(∑ i,x i^2) := mul_nonneg
    (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _)))
    (Finset.sum_nonneg (fun i _ => sq_nonneg _))
  by_cases hz : (∑ i,((A.mulVec x) i)^2)=0
  · rw [hz]; simpa using hf
  · have hp : 0 < ∑ i,((A.mulVec x) i)^2 := lt_of_le_of_ne hy (Ne.symm hz)
    nlinarith

end SkewLagrangeBound
#print axioms SkewLagrangeBound.bilinear_squared
