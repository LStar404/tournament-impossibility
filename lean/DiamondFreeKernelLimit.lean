import DiamondFreeKernelDeterminant
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

noncomputable section
open Filter Topology Matrix DiamondGap DiamondFreeKernelDeterminant
namespace DiamondFreeKernelLimit

/-- A moving parameter converging to z is allowed; this is stronger than a
fixed-point evaluation, but is not yet a quantitative uniform disk estimate. -/
theorem moving_binomial {w : ℕ → ℂ} {z : ℂ}
    (hw : Tendsto w atTop (𝓝 z)) :
    Tendsto (fun n => (1 + w n / (n : ℂ))^n) atTop (𝓝 (Complex.exp z)) := by
  apply Complex.tendsto_one_add_pow_exp_of_tendsto
  apply hw.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp

def finiteKernel (n : ℕ) (z : ℂ) : ℂ :=
  ((1 + z / (n : ℂ))^n + (1 - z / (n : ℂ))^n)/2

theorem moving_finiteKernel {w : ℕ → ℂ} {z : ℂ}
    (hw : Tendsto w atTop (𝓝 z)) :
    Tendsto (fun n => finiteKernel n (w n)) atTop (𝓝 (Complex.cosh z)) := by
  have hp := moving_binomial hw
  have hm := moving_binomial hw.neg
  simpa [finiteKernel, Complex.cosh, neg_div, sub_eq_add_neg] using
    (hp.add hm).div_const (2 : ℂ)

/-- Actual graph determinants converge without choosing compatible vertex
labels or compatible sign switches between successive orders. -/
theorem actual_moving_kernel (T : (n : ℕ) → Tournament (Fin n))
    (hT : ∀ n, (T n).diamonds.card = 0) {w : ℕ → ℂ} {z : ℂ}
    (hw : Tendsto w atTop (𝓝 z)) :
    Tendsto (fun n => (kernel (T n) (w n / (n : ℂ))).det)
      atTop (𝓝 (Complex.cosh z)) := by
  have he (n : ℕ) : (kernel (T n) (w n / (n : ℂ))).det = finiteKernel n (w n) := by
    simpa [finiteKernel] using zero_diamonds_kernel_det (T n) (hT n) (w n / (n : ℂ))
  simpa only [he] using moving_finiteKernel hw

theorem actual_imaginary_kernel (T : (n : ℕ) → Tournament (Fin n))
    (hT : ∀ n, (T n).diamonds.card = 0) {w : ℕ → ℂ} {z : ℂ}
    (hw : Tendsto w atTop (𝓝 z)) :
    Tendsto (fun n => (kernel (T n) (w n * Complex.I / (n : ℂ))).det)
      atTop (𝓝 (Complex.cos z)) := by
  simpa only [Complex.cosh_mul_I] using actual_moving_kernel T hT (hw.mul_const Complex.I)

/-- Reciprocal determinants converge at moving parameters whose limiting
cosine is nonzero. This is not an operator norm bound for matrix inverses. -/
theorem actual_imaginary_inverse (T : (n : ℕ) → Tournament (Fin n))
    (hT : ∀ n, (T n).diamonds.card = 0) {w : ℕ → ℂ} {z : ℂ}
    (hw : Tendsto w atTop (𝓝 z)) (hz : Complex.cos z ≠ 0) :
    Tendsto (fun n => ((kernel (T n) (w n * Complex.I / (n : ℂ))).det)⁻¹)
      atTop (𝓝 ((Complex.cos z)⁻¹)) :=
  (actual_imaginary_kernel T hT hw).inv₀ hz
/-- Eventual genuine two-sided matrix inverses, not merely Lean's totalized
inverse notation. No uniform operator norm estimate is asserted. -/
theorem actual_imaginary_invertible (T : (n : ℕ) → Tournament (Fin n))
    (hT : ∀ n, (T n).diamonds.card = 0) {w : ℕ → ℂ} {z : ℂ}
    (hw : Tendsto w atTop (𝓝 z)) (hz : Complex.cos z ≠ 0) :
    ∀ᶠ n in atTop,
      let A := kernel (T n) (w n * Complex.I / (n : ℂ))
      A * A⁻¹ = 1 ∧ A⁻¹ * A = 1 := by
  have hn := (actual_imaginary_kernel T hT hw).eventually_ne hz
  filter_upwards [hn] with n hn
  exact ⟨Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hn),
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hn)⟩

end DiamondFreeKernelLimit
#print axioms DiamondFreeKernelLimit.actual_moving_kernel
#print axioms DiamondFreeKernelLimit.actual_imaginary_inverse

#print axioms DiamondFreeKernelLimit.actual_imaginary_invertible
