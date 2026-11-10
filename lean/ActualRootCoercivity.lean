import ActualRootEnergy

/-! Verified in the 557-module direct-Lean compilation and declaration audit.
Depends on the ActualHessianFinite bridge, covered by the same verification.
The supplied spectral hypothesis is on the actual centered doubled block.
It is not an infinity-norm estimate, nor an assumed bound on the target root. -/
noncomputable section
namespace ActualRootCoercivity
open Finset Matrix
open FiniteSymmetricQuadratic ActualRootEnergy
variable {m : ℕ}
def centeredBlock (M : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ :=
  Matrix.fromBlocks 0 (ActualHessianFinite.centered M)
    (ActualHessianFinite.centered M).transpose 0

lemma perturbation_symmetric (M : Matrix (Fin m) (Fin m) ℝ)
    (i j : Fin m ⊕ Fin m) :
    ActualHessianFinite.perturbation M j i = ActualHessianFinite.perturbation M i j := by
  rcases i with i | i <;> rcases j with j | j
  all_goals simp [ActualHessianFinite.perturbation, Matrix.diagonal_apply,
    Matrix.transpose_apply, eq_comm]
  all_goals split_ifs with h <;> simp_all

lemma quad_add {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (z : ι → ℝ) : quad (A+B) z = quad A z + quad B z := by
  simp [quad, add_mul, Finset.sum_add_distrib]

/-- Exact mean block, before imposing the gauge balance. -/
lemma model_quadratic (M : Matrix (Fin m) (Fin m) ℝ) (x y : Fin m → ℝ) :
    quad (ActualHessianFinite.model M) (vector x y) =
      energy (vector x y) + quad (centeredBlock M) (vector x y) +
      2 / (m : ℝ) * (∑ i, x i) * (∑ j, y j) := by
  simp [quad, energy, ActualHessianFinite.model, centeredBlock, vector,
    Fintype.sum_sum_type, Matrix.one_apply, Matrix.transpose_apply,
    ActualHessianFinite.P, Matrix.add_apply, add_mul, mul_add,
    Finset.sum_add_distrib, Finset.sum_comm, ← Finset.mul_sum,
    ← Finset.sum_mul, mul_assoc, mul_left_comm, mul_comm]
  <;> ring

/-- All perturbation costs are 4ε, without a factor depending on m. -/
theorem actual_coercivity (hm : 0 < m) (M : Matrix (Fin m) (Fin m) ℝ)
    (x y : Fin m → ℝ) {q ε : ℝ} (hq : 0 ≤ q)
    (hQ : ‖Matrix.toEuclideanCLM (𝕜:=ℝ) (centeredBlock M)‖ ≤ q)
    (hr : ∀ i, |ActualHessianFinite.r M i| ≤ ε)
    (hc : ∀ j, |ActualHessianFinite.c M j| ≤ ε)
    (hbal : ∑ i, x i = ∑ j, y j) :
    (1-q-4*ε) * energy (vector x y) ≤
      quad (ActualHessianFinite.actual M) (vector x y) := by
  have hrow := ActualHessianFinite.perturbation_row_bound hm M hr hc
  have hE := symmetric_row_quadratic (ActualHessianFinite.perturbation M)
    (vector x y) (4*ε) (perturbation_symmetric M) hrow
  have hQlower := spectral_quadratic_lower (centeredBlock M) (vector x y) hq hQ
  have hmean : 0 ≤ 2/(m:ℝ)*(∑ i, x i)*(∑ j, y j) := by
    rw [← hbal]
    have hn : (0:ℝ) < m := by exact_mod_cast hm
    convert mul_nonneg (div_nonneg (show (0:ℝ) ≤ 2 by norm_num) hn.le)
      (sq_nonneg (∑ i, x i)) using 1 <;> ring
  rw [ActualHessianFinite.actual_eq_model_add, quad_add, model_quadratic]
  have hElo := (abs_le.mp hE).1
  nlinarith

/-- Final dimension-free actual-root estimate. Root existence is a separate theorem. -/
theorem actual_root_l2 (hm : 0 < m) (M : Matrix (Fin m) (Fin m) ℝ)
    (x y : Fin m → ℝ) {a q ε : ℝ} (ha : 0 ≤ a) (hq : 0 ≤ q)
    (hgap : 4*ε < 1-q)
    (hM : ∀ i j, 0 ≤ M i j)
    (hQ : ‖Matrix.toEuclideanCLM (𝕜:=ℝ) (centeredBlock M)‖ ≤ q)
    (hr : ∀ i, |ActualHessianFinite.r M i| ≤ ε)
    (hc : ∀ j, |ActualHessianFinite.c M j| ≤ ε)
    (hx : ∀ i, |x i| ≤ a) (hy : ∀ j, |y j| ≤ a)
    (hbal : ∑ i, x i = ∑ j, y j) (hroot : root M x y) :
    l2 (vector x y) ≤ Real.exp (2*a)/(1-q-4*ε) * l2 (residual M) := by
  exact root_l2_from_coercivity M x y ha (by linarith) hM hx hy hroot
    (actual_coercivity hm M x y hq hQ hr hc hbal)
end ActualRootCoercivity
#print axioms ActualRootCoercivity.perturbation_symmetric
#print axioms ActualRootCoercivity.model_quadratic
#print axioms ActualRootCoercivity.actual_coercivity
#print axioms ActualRootCoercivity.actual_root_l2
