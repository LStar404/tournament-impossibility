import RealGramEndpoint
import Mathlib
set_option autoImplicit false
noncomputable section
namespace RealBilinearTrace
open Matrix WithLp RealGramEndpoint
open scoped Matrix.Norms.L2Operator BigOperators InnerProductSpace
variable {r c : ℕ}
def fnorm (B : Matrix (Fin r) (Fin c) ℝ) : ℝ := ‖toLp 2 (fun ij : Fin r × Fin c => B ij.1 ij.2)‖
lemma fnorm_sq (B : Matrix (Fin r) (Fin c) ℝ) : fnorm B ^ 2 = frob B := by
  rw [fnorm, EuclideanSpace.real_norm_sq_eq]
  simp [frob, Fintype.sum_prod_type]
lemma sqrt_frob (B : Matrix (Fin r) (Fin c) ℝ) : Real.sqrt (frob B) = fnorm B := by
  rw [← fnorm_sq, Real.sqrt_sq (show 0 ≤ fnorm B from norm_nonneg _)]
lemma fnorm_add (B C : Matrix (Fin r) (Fin c) ℝ) : fnorm (B+C) ≤ fnorm B+fnorm C := by
  exact norm_add_le (toLp 2 (fun ij : Fin r × Fin c => B ij.1 ij.2))
    (toLp 2 (fun ij : Fin r × Fin c => C ij.1 ij.2))
lemma fnorm_smul (s : ℝ) (B : Matrix (Fin r) (Fin c) ℝ) : fnorm (s • B) = |s| * fnorm B := by
  exact norm_smul s (toLp 2 (fun ij : Fin r × Fin c => B ij.1 ij.2))
lemma bilinear_trace (B C : Matrix (Fin r) (Fin c) ℝ) (R : Matrix (Fin c) (Fin c) ℝ) :
    ‖(R*(Bᵀ*C)).trace‖ ≤ ‖R‖*fnorm B*fnorm C := by
  let b : Fin r → ℝ := fun i => ‖toLp 2 (fun j => B i j)‖
  let d : Fin r → ℝ := fun i => ‖toLp 2 (fun j => C i j)‖
  have row (i : Fin r) : ‖(C*R*Bᵀ) i i‖ ≤ ‖R‖*(b i*d i) := by
    let x := toLp 2 (fun j => C i j)
    let y := toLp 2 (fun j => B i j)
    have hh := norm_inner_le_norm (𝕜:=ℝ) x ((Matrix.toEuclideanCLM (𝕜:=ℝ) R) y)
    have hi : ⟪x, (Matrix.toEuclideanCLM (𝕜:=ℝ) R) y⟫_ℝ = (C*R*Bᵀ) i i := by
      rw [Matrix.mul_assoc]
      simp [x, y, EuclideanSpace.inner_eq_star_dotProduct, Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
    rw [hi] at hh
    calc
      _ ≤ ‖x‖ * ‖(Matrix.toEuclideanCLM (𝕜:=ℝ) R) y‖ := hh
      _ ≤ ‖x‖ * (‖Matrix.toEuclideanCLM (𝕜:=ℝ) R‖*‖y‖) :=
        mul_le_mul_of_nonneg_left ((Matrix.toEuclideanCLM (𝕜:=ℝ) R).le_opNorm y) (norm_nonneg _)
      _ = _ := by rw [Matrix.l2_opNorm_toEuclideanCLM]; dsimp [b,d,x,y]; ring
  have hb : ∑ i, b i^2 = frob B := by simp [b, frob, EuclideanSpace.real_norm_sq_eq]
  have hd : ∑ i, d i^2 = frob C := by simp [d, frob, EuclideanSpace.real_norm_sq_eq]
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ b d
  rw [hb, hd, sqrt_frob, sqrt_frob] at hcs
  have ht : (R*(Bᵀ*C)).trace = (C*R*Bᵀ).trace := by rw [Matrix.trace_mul_cycle', Matrix.mul_assoc]
  rw [ht]
  calc
    _ ≤ ∑ i, ‖(C*R*Bᵀ) i i‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖R‖*(b i*d i) := Finset.sum_le_sum fun i _ => row i
    _ = ‖R‖*∑ i, b i*d i := by rw [Finset.mul_sum]
    _ ≤ ‖R‖*(fnorm B*fnorm C) := mul_le_mul_of_nonneg_left hcs (norm_nonneg _)
    _ = _ := by ring
end RealBilinearTrace
