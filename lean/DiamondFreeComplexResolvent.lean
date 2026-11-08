import DiamondFreeKernelLimit

noncomputable section
open Matrix Filter Topology DiamondGap DiamondFreeKernelDeterminant DiamondFreeKernelLimit
namespace DiamondFreeComplexResolvent

def resolventMatrix {n : ℕ} (T : Tournament (Fin n)) (w : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  1 + (w / (n : ℂ))^2 • (signMatrix T * signMatrix T)

/-- The exact quadratic resolvent denominator factors into the two linear
kernels, before any inverse or analytic limit is taken. -/
theorem factorization {n : ℕ} (T : Tournament (Fin n)) (w : ℂ) :
    resolventMatrix T w =
      kernel T (w * Complex.I / (n : ℂ)) * kernel T (-(w * Complex.I / (n : ℂ))) := by
  let a : ℂ := w * Complex.I / (n : ℂ)
  let S : Matrix (Fin n) (Fin n) ℂ := signMatrix T
  have ha : -(a*a) = (w / (n : ℂ))^2 := by
    dsimp [a]
    simp only [div_eq_mul_inv]
    ring_nf
    simp [Complex.I_sq]
  have hprod : (a • S) * (a • S) = (a*a) • (S*S) := by
    simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hid (X : Matrix (Fin n) (Fin n) ℂ) : (1+X)*(1-X)=1-X*X := by
    noncomm_ring
  have hm := hid (a • S)
  change 1 + (w / (n : ℂ))^2 • (S*S) = (1 + a • S) * (1 + (-a) • S)
  rw [neg_smul, ← sub_eq_add_neg, hm, hprod, sub_eq_add_neg, ← neg_smul, ha]

 theorem actual_det (T : (n : ℕ) → Tournament (Fin n))
    (hT : ∀ n, (T n).diamonds.card = 0) (n : ℕ) (w : ℂ) :
    (resolventMatrix (T n) w).det = (finiteKernel n (w * Complex.I))^2 := by
  rw [factorization, det_mul, zero_diamonds_kernel_det _ (hT n),
    zero_diamonds_kernel_det _ (hT n)]
  simp [finiteKernel, Fintype.card_fin, neg_div, sub_eq_add_neg, add_comm, pow_two]

theorem det_tendsto (T : (n : ℕ) → Tournament (Fin n))
    (hT : ∀ n, (T n).diamonds.card = 0) {w : ℕ → ℂ} {z : ℂ}
    (hw : Tendsto w atTop (𝓝 z)) :
    Tendsto (fun n => (resolventMatrix (T n) (w n)).det) atTop (𝓝 ((Complex.cos z)^2)) := by
  simp_rw [actual_det T hT]
  simpa only [Complex.cosh_mul_I] using
    (moving_finiteKernel (hw.mul_const Complex.I)).pow 2

theorem eventually_inverse (T : (n : ℕ) → Tournament (Fin n))
    (hT : ∀ n, (T n).diamonds.card = 0) {w : ℕ → ℂ} {z : ℂ}
    (hw : Tendsto w atTop (𝓝 z)) (hz : Complex.cos z ≠ 0) :
    ∀ᶠ n in atTop,
      let A := resolventMatrix (T n) (w n)
      A * A⁻¹ = 1 ∧ A⁻¹ * A = 1 := by
  have hn := (det_tendsto T hT hw).eventually_ne (pow_ne_zero 2 hz)
  filter_upwards [hn] with n hn
  exact ⟨Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hn),
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hn)⟩
end DiamondFreeComplexResolvent
#print axioms DiamondFreeComplexResolvent.factorization
#print axioms DiamondFreeComplexResolvent.eventually_inverse
