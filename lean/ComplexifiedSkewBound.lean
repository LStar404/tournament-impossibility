import SkewLagrangeBound
noncomputable section
namespace ComplexifiedSkewBound
open Matrix WithLp
variable {I : Type*} [Fintype I] [DecidableEq I]
def complexify (A : Matrix I I ℝ) : Matrix I I ℂ := fun i j => (A i j : ℂ)

theorem vector_squared (A : Matrix I I ℝ) (hA : ∀ i j,A j i= -A i j)
    (x : I → ℂ) :
    2*‖toLp 2 ((complexify A).mulVec x)‖^2 ≤
      (∑ i,∑ j,A i j^2)*‖toLp 2 x‖^2 := by
  have hr := SkewLagrangeBound.vector_squared A hA (fun i => (x i).re)
  have hi := SkewLagrangeBound.vector_squared A hA (fun i => (x i).im)
  have hre (i : I) : (((complexify A).mulVec x) i).re =
      (A.mulVec (fun j => (x j).re)) i := by
    simp [complexify,Matrix.mulVec,dotProduct,Complex.mul_re]
  have him (i : I) : (((complexify A).mulVec x) i).im =
      (A.mulVec (fun j => (x j).im)) i := by
    simp [complexify,Matrix.mulVec,dotProduct,Complex.mul_im]
  simp only [EuclideanSpace.norm_sq_eq,Complex.sq_norm,Complex.normSq_apply,
    ← sq, hre,him,Finset.sum_add_distrib]
  nlinarith

theorem operator_bound (A : Matrix I I ℝ) (hA : ∀ i j,A j i= -A i j)
    (q : ℝ) (hq : 0 ≤ q) (hf : (∑ i,∑ j,A i j^2) ≤ 2*q^2) :
    ‖Matrix.toEuclideanCLM (𝕜:=ℂ) (complexify A)‖ ≤ q := by
  apply ContinuousLinearMap.opNorm_le_bound _ hq
  intro x
  have hv := vector_squared A hA (ofLp x)
  have hh : toLp 2 ((complexify A).mulVec (ofLp x)) =
      Matrix.toEuclideanCLM (𝕜:=ℂ) (complexify A) x := by
    apply WithLp.ofLp_injective
    rw [Matrix.ofLp_toEuclideanCLM]
  rw [hh] at hv
  simp only [toLp_ofLp] at hv
  have hp := mul_le_mul_of_nonneg_right hf (sq_nonneg ‖x‖)
  have hn := norm_nonneg (Matrix.toEuclideanCLM (𝕜:=ℂ) (complexify A) x)
  have hx := norm_nonneg x
  nlinarith [mul_nonneg hq hx]
end ComplexifiedSkewBound
#print axioms ComplexifiedSkewBound.operator_bound
