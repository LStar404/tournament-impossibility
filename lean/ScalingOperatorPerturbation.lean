import FiniteSchurBound
import ScalingDensityFrobenius

/-! Verified in the 557-module direct-Lean compilation and declaration audit. Actual scaling difference, not an assumed
row/column-error matrix. Centered spectral projection is a separate step. -/
set_option autoImplicit false
noncomputable section
namespace ScalingOperatorPerturbation
open Matrix Finset MatrixScalingMassPotential ScalingDensityFrobenius
variable {α : Type*} [Fintype α] [DecidableEq α]

lemma exp_error_uniform {b t : ℝ} (hb : 0 ≤ b) (ht : |t| ≤ b) :
    |Real.exp t-1| ≤ Real.exp b-1 := by
  obtain ⟨htlo,hthi⟩ := abs_le.mp ht
  have he := Real.add_one_le_exp b
  have htE := Real.add_one_le_exp t
  have hupper := Real.exp_le_exp.mpr hthi
  rw [abs_le]
  constructor <;> linarith

lemma exp_error_nonnegative {b : ℝ} (hb : 0 ≤ b) : 0 ≤ Real.exp b-1 := by
  have hh := Real.add_one_le_exp b
  linarith

lemma difference_entry (M : Matrix α α ℝ) (x y : α → ℝ) {a : ℝ}
    (ha : 0 ≤ a) (hM : ∀ i j, 0 ≤ M i j)
    (hx : ∀ i, |x i| ≤ a) (hy : ∀ j, |y j| ≤ a) (i j : α) :
    |(expScaled M x y-M) i j| ≤ (Real.exp (2*a)-1)*M i j := by
  have ht := exp_error_uniform (by linarith : 0 ≤ 2*a) (sum_abs_bound x y hx hy i j)
  have hid : (expScaled M x y-M) i j = M i j*(Real.exp (x i+y j)-1) := by
    simp [expScaled]
    ring
  rw [hid, abs_mul, abs_of_nonneg (hM i j)]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left ht (hM i j)

theorem row_bound (M : Matrix α α ℝ) (x y : α → ℝ) {a S : ℝ}
    (ha : 0 ≤ a) (hM : ∀ i j, 0 ≤ M i j)
    (hr : ∀ i, (∑ j, M i j) ≤ S)
    (hx : ∀ i, |x i| ≤ a) (hy : ∀ j, |y j| ≤ a) (i : α) :
    (∑ j, |(expScaled M x y-M) i j|) ≤ S*(Real.exp (2*a)-1) := by
  calc
    _ ≤ ∑ j, (Real.exp (2*a)-1)*M i j :=
      Finset.sum_le_sum (fun j _ => difference_entry M x y ha hM hx hy i j)
    _ = (Real.exp (2*a)-1)*(∑ j, M i j) := by rw [Finset.mul_sum]
    _ ≤ (Real.exp (2*a)-1)*S :=
      mul_le_mul_of_nonneg_left (hr i) (exp_error_nonnegative (by linarith))
    _ = _ := mul_comm _ _

theorem col_bound (M : Matrix α α ℝ) (x y : α → ℝ) {a S : ℝ}
    (ha : 0 ≤ a) (hM : ∀ i j, 0 ≤ M i j)
    (hc : ∀ j, (∑ i, M i j) ≤ S)
    (hx : ∀ i, |x i| ≤ a) (hy : ∀ j, |y j| ≤ a) (j : α) :
    (∑ i, |(expScaled M x y-M) i j|) ≤ S*(Real.exp (2*a)-1) := by
  calc
    _ ≤ ∑ i, (Real.exp (2*a)-1)*M i j :=
      Finset.sum_le_sum (fun i _ => difference_entry M x y ha hM hx hy i j)
    _ = (Real.exp (2*a)-1)*(∑ i, M i j) := by rw [Finset.mul_sum]
    _ ≤ (Real.exp (2*a)-1)*S :=
      mul_le_mul_of_nonneg_left (hc j) (exp_error_nonnegative (by linarith))
    _ = _ := mul_comm _ _

theorem real_operator_bound (M : Matrix α α ℝ) (x y : α → ℝ) {a S : ℝ}
    (ha : 0 ≤ a) (hS : 0 ≤ S) (hM : ∀ i j, 0 ≤ M i j)
    (hr : ∀ i, (∑ j, M i j) ≤ S) (hc : ∀ j, (∑ i, M i j) ≤ S)
    (hx : ∀ i, |x i| ≤ a) (hy : ∀ j, |y j| ≤ a) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (expScaled M x y-M)‖ ≤ S*(Real.exp (2*a)-1) :=
  FiniteSchurBound.operator_bound_same _
    (mul_nonneg hS (exp_error_nonnegative (by linarith)))
    (row_bound M x y ha hM hr hx hy) (col_bound M x y ha hM hc hx hy)

theorem complex_operator_bound (M : Matrix α α ℝ) (x y : α → ℝ) {a S : ℝ}
    (ha : 0 ≤ a) (hS : 0 ≤ S) (hM : ∀ i j, 0 ≤ M i j)
    (hr : ∀ i, (∑ j, M i j) ≤ S) (hc : ∀ j, (∑ i, M i j) ≤ S)
    (hx : ∀ i, |x i| ≤ a) (hy : ∀ j, |y j| ≤ a) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ)
      (ActualHessianComplex.realComplex (expScaled M x y-M))‖ ≤ S*(Real.exp (2*a)-1) :=
  ActualHessianComplex.realComplex_gap _
    (mul_nonneg hS (exp_error_nonnegative (by linarith)))
    (real_operator_bound M x y ha hS hM hr hc hx hy)
end ScalingOperatorPerturbation
#print axioms ScalingOperatorPerturbation.real_operator_bound
#print axioms ScalingOperatorPerturbation.complex_operator_bound
