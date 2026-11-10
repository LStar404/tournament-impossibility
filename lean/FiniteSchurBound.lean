import ActualHessianComplex
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! Verified in the 557-module direct-Lean compilation and declaration audit. Real finite Schur test and complexification.
No square-root weights, inverse hypotheses, or dimension factor. -/
set_option autoImplicit false
noncomputable section
namespace FiniteSchurBound
open Matrix Finset WithLp
variable {α : Type*} [Fintype α] [DecidableEq α]

lemma row_square (A : Matrix α α ℝ) (v : α → ℝ) (i : α) :
    ((A *ᵥ v) i)^2 ≤ (∑ j, |A i j|)*(∑ j, |A i j| *(v j)^2) := by
  have ht : |(A *ᵥ v) i| ≤ ∑ j, |A i j| *|v j| := by
    simpa [Matrix.mulVec, dotProduct, abs_mul] using
      Finset.abs_sum_le_sum_abs (fun j => A i j*v j) Finset.univ
  have hnon : 0 ≤ ∑ j, |A i j| *|v j| :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hsq := (sq_le_sq₀ (abs_nonneg _) hnon).mpr ht
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (r := fun j => |A i j| *|v j|) (f := fun j => |A i j|)
    (g := fun j => |A i j| *(v j)^2) Finset.univ
    (fun j _ => abs_nonneg _) (fun j _ => mul_nonneg (abs_nonneg _) (sq_nonneg _))
    (fun j _ => by simp only [mul_pow, sq_abs]; nlinarith [sq_abs (A i j)])
  have hs : ((A *ᵥ v) i)^2 ≤ (∑ j, |A i j| * |v j|)^2 := by
    simpa only [sq_abs] using hsq
  exact hs.trans hcs

theorem energy_bound (A : Matrix α α ℝ) (v : α → ℝ) {R C : ℝ}
    (hR : 0 ≤ R) (hrow : ∀ i, (∑ j, |A i j|) ≤ R)
    (hcol : ∀ j, (∑ i, |A i j|) ≤ C) :
    (∑ i, ((A *ᵥ v) i)^2) ≤ (R*C)*(∑ j, (v j)^2) := by
  calc
    _ ≤ ∑ i, R*(∑ j, |A i j| *(v j)^2) := by
      apply Finset.sum_le_sum
      intro i _
      exact (row_square A v i).trans (mul_le_mul_of_nonneg_right (hrow i)
        (Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (sq_nonneg _))))
    _ = R*(∑ j, (∑ i, |A i j|)*(v j)^2) := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul]
    _ ≤ R*(∑ j, C*(v j)^2) := by
      apply mul_le_mul_of_nonneg_left _ hR
      exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hcol j) (sq_nonneg _))
    _ = _ := by rw [← Finset.mul_sum]; ring

theorem operator_bound (A : Matrix α α ℝ) {R C : ℝ}
    (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hrow : ∀ i, (∑ j, |A i j|) ≤ R) (hcol : ∀ j, (∑ i, |A i j|) ≤ C) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ ≤ Real.sqrt (R*C) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro v
  have he := energy_bound A (ofLp v) hR hrow hcol
  have henergy : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A v‖^2 ≤ (R*C)*‖v‖^2 := by
    simpa [EuclideanSpace.norm_sq_eq, Matrix.ofLp_toEuclideanCLM,
      Real.norm_eq_abs, sq_abs] using he
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  simpa only [mul_pow, Real.sq_sqrt (mul_nonneg hR hC)] using henergy

theorem operator_bound_same (A : Matrix α α ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hrow : ∀ i, (∑ j, |A i j|) ≤ K) (hcol : ∀ j, (∑ i, |A i j|) ≤ K) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ ≤ K := by
  have hh := operator_bound A hK hK hrow hcol
  simpa [← pow_two, Real.sqrt_sq hK] using hh

theorem complex_operator_bound (A : Matrix α α ℝ) {R C : ℝ}
    (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hrow : ∀ i, (∑ j, |A i j|) ≤ R) (hcol : ∀ j, (∑ i, |A i j|) ≤ C) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (ActualHessianComplex.realComplex A)‖ ≤ Real.sqrt (R*C) :=
  ActualHessianComplex.realComplex_gap A (Real.sqrt_nonneg _) (operator_bound A hR hC hrow hcol)
end FiniteSchurBound
#print axioms FiniteSchurBound.energy_bound
#print axioms FiniteSchurBound.operator_bound
#print axioms FiniteSchurBound.complex_operator_bound
