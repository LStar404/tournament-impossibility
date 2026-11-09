import MatrixEuclideanEntryBound

noncomputable section
namespace EuclideanBilinearContraction
open Matrix WithLp
open scoped InnerProductSpace
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem bilinear (x y : I → ℂ) :
    ‖x ⬝ᵥ y‖ ≤ ‖toLp 2 x‖*‖toLp 2 y‖ := by
  have hh := norm_inner_le_norm (𝕜:=ℂ) (toLp 2 (star x)) (toLp 2 y)
  have he : ⟪toLp 2 (star x),toLp 2 y⟫_ℂ=x ⬝ᵥ y := by
    simp [EuclideanSpace.inner_eq_star_dotProduct,dotProduct_comm]
  rw [he] at hh
  have hn : ‖toLp 2 (star x)‖=‖toLp 2 x‖ := by
    rw [EuclideanSpace.norm_eq,EuclideanSpace.norm_eq]
    simp
  simpa only [hn] using hh

theorem matrix_bilinear (x y : I → ℂ) (R : Matrix I I ℂ) :
    ‖x ⬝ᵥ (R.mulVec y)‖ ≤ ‖toLp 2 x‖*‖Matrix.toEuclideanCLM (𝕜:=ℂ) R‖*‖toLp 2 y‖ := by
  have hm := (Matrix.toEuclideanCLM (𝕜:=ℂ) R).le_opNorm (toLp 2 y)
  have he : ‖toLp 2 (R.mulVec y)‖ ≤ ‖Matrix.toEuclideanCLM (𝕜:=ℂ) R‖*‖toLp 2 y‖ := by
    have hv : toLp 2 (R.mulVec y)=(Matrix.toEuclideanCLM (𝕜:=ℂ) R) (toLp 2 y) := by
      apply WithLp.ofLp_injective
      rw [Matrix.ofLp_toEuclideanCLM]
    rw [hv]
    exact hm
  exact (bilinear x _).trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left he (norm_nonneg (toLp 2 x)))

theorem matrix_entry (Q R : Matrix I I ℂ) (i j : I) :
    ‖(Q*R*Q) i j‖ ≤ ‖toLp 2 (fun a => Q i a)‖*
      ‖Matrix.toEuclideanCLM (𝕜:=ℂ) R‖*‖toLp 2 (fun a => Q a j)‖ := by
  have he : (Q*R*Q) i j=(fun a => Q i a) ⬝ᵥ R.mulVec (fun a => Q a j) := by
    rw [Matrix.mul_assoc]
    rfl
  rw [he]
  exact matrix_bilinear _ _ _
end EuclideanBilinearContraction
#print axioms EuclideanBilinearContraction.matrix_entry
