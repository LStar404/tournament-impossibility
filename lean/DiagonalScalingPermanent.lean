import MatrixScalingMassPotential

/-!
Exact permanent recovery under finite exponential diagonal scaling, followed by
the mass-potential upper bound. Focused compiled candidate. No scaling-existence or
permanent-asymptotic assertion is made here.
-/
noncomputable section
namespace DiagonalScalingPermanent
open Finset MatrixScalingMassPotential
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Row factors are indexed by sigma i in mathlib's permanent convention. -/
lemma permutation_potential (σ : Equiv.Perm α) (x y : α → ℝ) :
    (∑ i, (x (σ i) + y i)) = theta x y := by
  rw [sum_add_distrib, Equiv.sum_comp]
  rfl

/-- No balance or nonnegativity is needed for this exact algebraic identity. -/
theorem permanent_expScaled (M : Matrix α α ℝ) (x y : α → ℝ) :
    (expScaled M x y).permanent = Real.exp (theta x y) * M.permanent := by
  unfold Matrix.permanent
  have hterm (σ : Equiv.Perm α) :
      (∏ i, expScaled M x y (σ i) i) =
        Real.exp (theta x y) * ∏ i, M (σ i) i := by
    simp only [expScaled, prod_mul_distrib]
    rw [← Real.exp_sum, permutation_potential]
    ring
  simp_rw [hterm]
  rw [← mul_sum]

/-- Inverse recovery has the negative potential, not its positive exponential. -/
theorem permanent_recovery (M : Matrix α α ℝ) (x y : α → ℝ) :
    M.permanent = Real.exp (-theta x y) * (expScaled M x y).permanent := by
  rw [permanent_expScaled, ← mul_assoc, ← Real.exp_add, neg_add_cancel,
    Real.exp_zero, one_mul]

lemma permanent_nonneg (N : Matrix α α ℝ) (hN : ∀ i j, 0 ≤ N i j) :
    0 ≤ N.permanent := by
  unfold Matrix.permanent
  exact sum_nonneg (fun σ _ => prod_nonneg (fun i _ => hN (σ i) i))

/-- Derived recovery bound, conditional only on an actually existing scaling.
The target mass-potential or permanent inequality is not taken as a hypothesis. -/
theorem permanent_le_exp_kappa (M : Matrix α α ℝ) (x y : α → ℝ)
    (hM : ∀ i j, 0 ≤ M i j)
    (hrow : ∀ i, (∑ j, expScaled M x y i j) = 1)
    (hcol : ∀ j, (∑ i, expScaled M x y i j) = 1) :
    M.permanent ≤ Real.exp (kappa M) * (expScaled M x y).permanent := by
  rw [permanent_recovery M x y]
  exact mul_le_mul_of_nonneg_right (exp_neg_theta_le_exp_kappa M x y hM hrow hcol)
    (permanent_nonneg _ (expScaled_nonneg M x y hM))

end DiagonalScalingPermanent
#print axioms DiagonalScalingPermanent.permanent_expScaled
#print axioms DiagonalScalingPermanent.permanent_recovery
#print axioms DiagonalScalingPermanent.permanent_le_exp_kappa
