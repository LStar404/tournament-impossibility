import FiniteSymmetricQuadratic

/-! Verified in the 557-module direct-Lean compilation and declaration audit.
An estimate for an actual supplied root, not root existence.
The finite Hessian is ActualHessianFinite.actual, not an averaged operator. -/
noncomputable section
namespace ActualRootEnergy
open Finset Matrix
open FiniteSymmetricQuadratic
variable {m : ℕ}
abbrev I (m : ℕ) := Fin m

def residual (M : Matrix ((Fin m)) ((Fin m)) ℝ) : ((Fin m) ⊕ (Fin m)) → ℝ :=
  Sum.elim (ActualHessianFinite.r M) (ActualHessianFinite.c M)
def vector (x y : (Fin m) → ℝ) : ((Fin m) ⊕ (Fin m)) → ℝ := Sum.elim x y

def root (M : Matrix ((Fin m)) ((Fin m)) ℝ) (x y : (Fin m) → ℝ) : Prop :=
  (∀ i, (∑ j, M i j * Real.exp (x i + y j)) = 1) ∧
  (∀ j, (∑ i, M i j * Real.exp (x i + y j)) = 1)

/-- Derived from exp convexity on each side of zero; no mean-value integral. -/
theorem exp_secant_lower {a s : ℝ} (ha : 0 ≤ a) (hs : |s| ≤ 2*a) :
    Real.exp (-2*a) * s^2 ≤ (Real.exp s - 1)*s := by
  have he : 0 < Real.exp s := Real.exp_pos _
  have hlo : Real.exp (-2*a) ≤ Real.exp s := Real.exp_le_exp.mpr (by linarith [(abs_le.mp hs).1])
  have hunit : Real.exp (-2*a) ≤ 1 := by
    simpa using Real.exp_le_exp.mpr (show -2*a ≤ 0 by linarith)
  by_cases hpos : 0 ≤ s
  · have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp s) hpos
    have h' := mul_le_mul_of_nonneg_right hunit (sq_nonneg s)
    nlinarith
  · have hsneg : s ≤ 0 := le_of_not_ge hpos
    have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-s)) he.le
    have hex : Real.exp s * Real.exp (-s) = 1 := by rw [← Real.exp_add]; simp
    rw [hex] at h
    have hprod : Real.exp s - 1 ≤ (Real.exp s)*s := by nlinarith
    have hprod' := mul_le_mul_of_nonpos_right hprod hsneg
    have hlow := mul_le_mul_of_nonneg_right hlo (sq_nonneg s)
    nlinarith

/-- Both row and column root equations are used; nothing is assumed about the energy. -/
theorem root_identity (M : Matrix (Fin m) (Fin m) ℝ) (x y : (Fin m) → ℝ) (hroot : root M x y) :
    -(∑ k, residual M k * vector x y k) =
      ∑ i, ∑ j, M i j * (Real.exp (x i + y j)-1) * (x i+y j) := by
  have hexpand : (∑ i, ∑ j, M i j * (Real.exp (x i+y j)-1)*(x i+y j)) =
      (∑ i, x i * ((∑ j, M i j * Real.exp (x i+y j)) - ActualHessianFinite.row M i)) +
      (∑ j, y j * ((∑ i, M i j * Real.exp (x i+y j)) - ActualHessianFinite.col M j)) := by
    simp only [ActualHessianFinite.row, ActualHessianFinite.col,
      Finset.mul_sum, mul_sub, Finset.sum_sub_distrib]
    rw [Finset.sum_comm (f := fun j i => y j * (M i j * Real.exp (x i+y j))),
      Finset.sum_comm (f := fun j i => y j * M i j)]
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _; ring
  rw [hexpand]
  simp only [hroot.1, hroot.2, residual, vector, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr, ActualHessianFinite.r, ActualHessianFinite.c]
  simp only [neg_add, ← Finset.sum_neg_distrib]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

/-- Literal finite Hessian quadratic, derived by finite regrouping. -/
theorem actual_quadratic (M : Matrix (Fin m) (Fin m) ℝ) (x y : (Fin m) → ℝ) :
    quad (ActualHessianFinite.actual M) (vector x y) =
      ∑ i, ∑ j, M i j * (x i+y j)^2 := by
  simp only [quad, ActualHessianFinite.actual, vector, Fintype.sum_sum_type,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Matrix.transpose_apply, Sum.elim_inl, Sum.elim_inr,
    Finset.sum_add_distrib]
  simp [Matrix.diagonal_apply, ActualHessianFinite.row, ActualHessianFinite.col,
    Finset.sum_mul, Finset.mul_sum, add_sq,
    Finset.sum_add_distrib, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm]
  rw [Finset.sum_comm (f := fun j i => M i j * (x i * y j)),
    Finset.sum_comm (f := fun j i => M i j * (y j * y j))]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _; ring

/-- Finite energy inequality retaining the actual Hessian and actual root. -/
theorem root_energy (M : Matrix (Fin m) (Fin m) ℝ) (x y : (Fin m) → ℝ) {a : ℝ}
    (ha : 0 ≤ a) (hM : ∀ i j, 0 ≤ M i j)
    (hx : ∀ i, |x i| ≤ a) (hy : ∀ j, |y j| ≤ a) (hr : root M x y) :
    Real.exp (-2*a) * quad (ActualHessianFinite.actual M) (vector x y) ≤
      -(∑ k, residual M k * vector x y k) := by
  rw [root_identity M x y hr, actual_quadratic, Finset.mul_sum]
  apply Finset.sum_le_sum; intro i _; rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro j _
  have hs : |x i+y j| ≤ 2*a := (abs_add_le _ _).trans (by linarith [hx i,hy j])
  have h := mul_le_mul_of_nonneg_left (exp_secant_lower ha hs) (hM i j)
  nlinarith

/-- Cauchy--Schwarz and cancellation, including the zero-vector case.
The coercivity premise is discharged for actual H in ActualRootCoercivity. -/
theorem root_l2_from_coercivity (M : Matrix (Fin m) (Fin m) ℝ) (x y : (Fin m) → ℝ) {a c : ℝ}
    (ha : 0 ≤ a) (hc : 0 < c) (hM : ∀ i j, 0 ≤ M i j)
    (hx : ∀ i, |x i| ≤ a) (hy : ∀ j, |y j| ≤ a) (hr : root M x y)
    (hco : c * energy (vector x y) ≤ quad (ActualHessianFinite.actual M) (vector x y)) :
    l2 (vector x y) ≤ Real.exp (2*a) / c * l2 (residual M) := by
  have hE := root_energy M x y ha hM hx hy hr
  have hC := mul_le_mul_of_nonneg_left hco (Real.exp_pos (-2*a)).le
  have hCS := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset ((Fin m) ⊕ (Fin m)))
    (fun k => -residual M k) (vector x y)
  have hCS' : -(∑ k, residual M k * vector x y k) ≤
      l2 (residual M) * l2 (vector x y) := by
    simpa [l2, energy, neg_mul, Finset.sum_neg_distrib] using hCS
  have hz := Real.sqrt_nonneg (energy (vector x y))
  have hz2 : l2 (vector x y)^2 = energy (vector x y) := Real.sq_sqrt (energy_nonneg _)
  by_cases hzero : l2 (vector x y) = 0
  · rw [hzero]; exact mul_nonneg (div_nonneg (Real.exp_pos _).le hc.le) (Real.sqrt_nonneg _)
  have hp : 0 < l2 (vector x y) := lt_of_le_of_ne hz (Ne.symm hzero)
  have hprod : (Real.exp (-2*a)*c*l2 (vector x y))*l2 (vector x y) ≤
      l2 (residual M)*l2 (vector x y) := by
    calc
      _ = Real.exp (-2*a) * (c * energy (vector x y)) := by rw [← hz2]; ring
      _ ≤ _ := hC.trans (hE.trans hCS')
  have hcancel := (mul_le_mul_iff_left₀ hp).mp hprod
  have hex : Real.exp (2*a)*Real.exp (-2*a)=1 := by rw [← Real.exp_add]; simp
  have hm := mul_le_mul_of_nonneg_left hcancel (Real.exp_pos (2*a)).le
  have hfinal : l2 (vector x y) * c ≤ Real.exp (2*a) * l2 (residual M) := by
    have heq : Real.exp (2*a) * (Real.exp (-2*a)*c*l2 (vector x y)) = l2 (vector x y)*c := by
      calc
        _ = (Real.exp (2*a)*Real.exp (-2*a))*(l2 (vector x y)*c) := by ring
        _ = _ := by rw [hex, one_mul]
    rw [heq] at hm
    exact hm
  simpa [div_mul_eq_mul_div] using (le_div_iff₀ hc).mpr hfinal
end ActualRootEnergy
#print axioms ActualRootEnergy.exp_secant_lower
#print axioms ActualRootEnergy.root_identity
#print axioms ActualRootEnergy.actual_quadratic
#print axioms ActualRootEnergy.root_energy
#print axioms ActualRootEnergy.root_l2_from_coercivity
