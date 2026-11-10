import ScalingOperatorPerturbation
import PermanentCircleActualCentering

/-! Verified in the 557-module direct-Lean compilation and declaration audit. Final centered spectral gap for an ACTUAL
scaling with raw unit marginals. Uses the repository's genuine averaging
orthogonal projection, rather than assuming a compression identity. -/
set_option autoImplicit false
noncomputable section
namespace ScalingCenteredGap
open Matrix Finset ActualHessianFinite ActualHessianComplex MatrixScalingMassPotential
variable {m : ℕ}

lemma cast_P : realComplex (P m) = PermanentSpectralFrame.averaging m := by
  ext i j
  simp [realComplex, P, PermanentSpectralFrame.averaging]

lemma cast_Pi : realComplex (1-P m) = 1-PermanentSpectralFrame.averaging m := by
  ext i j
  simp [realComplex, P, PermanentSpectralFrame.averaging, Matrix.one_apply]
  split_ifs <;> norm_num

/-- Genuine self-adjoint idempotence and the dimension-free contraction bound. -/
theorem projection_data (hm : 0 < m) :
    (realComplex (1-P m))ᴴ = realComplex (1-P m) ∧
    realComplex (1-P m)*realComplex (1-P m) = realComplex (1-P m) ∧
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I m) (realComplex (1-P m))‖ ≤ 1 := by
  rw [cast_Pi]
  exact ⟨PermanentSpectralFrame.complement_adjoint,
    PermanentSpectralFrame.complement_square hm,
    PermanentSpectralFrame.complement_op_norm_le_one hm⟩

lemma doubly_stochastic_centering (hm : 0 < m) (N : Matrix (I m) (I m) ℝ)
    (hr : ∀ i, (∑ j, N i j) = 1) (hc : ∀ j, (∑ i, N i j) = 1) :
    N-P m = (1-P m)*N*(1-P m) := by
  have hcenter : centered N = N-P m := by
    ext i j
    simp [centered, correction, mu, r, c, ActualHessianFinite.row, ActualHessianFinite.col, hr, hc]
  rw [← hcenter]
  exact centered_projection hm N

lemma centered_decomposition (hm : 0 < m) (M N : Matrix (I m) (I m) ℝ)
    (hr : ∀ i, (∑ j, N i j) = 1) (hc : ∀ j, (∑ i, N i j) = 1) :
    N-P m = (1-P m)*M*(1-P m)+(1-P m)*(N-M)*(1-P m) := by
  rw [doubly_stochastic_centering hm N hr hc]
  simp only [Matrix.mul_sub, Matrix.sub_mul]
  abel

lemma compressed_norm (hm : 0 < m) (D : Matrix (I m) (I m) ℝ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I m) (realComplex ((1-P m)*D*(1-P m)))‖ ≤
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I m) (realComplex D)‖ := by
  have hp := (projection_data hm).2.2
  rw [realComplex_mul, realComplex_mul, map_mul, map_mul]
  calc
    _ ≤ (‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I m) (realComplex (1-P m))‖ *
        ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I m) (realComplex D)‖) *
        ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I m) (realComplex (1-P m))‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1*‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I m) (realComplex D)‖)*1 := by gcongr
    _ = _ := by ring

/-- Raw spectral gap on M plus actual row/column normalization of its scaled N.
The result is q+S(exp(2a)-1); obtaining a fixed gap <1 additionally requires
this explicit number to be <1. No nonlinear root/existence is asserted here. -/
theorem actual_scaled_centered_gap (hm : 0 < m)
    (M : Matrix (I m) (I m) ℝ) (x y : I m → ℝ) {a S q : ℝ}
    (ha : 0 ≤ a) (hS : 0 ≤ S) (hq : 0 ≤ q)
    (hM : ∀ i j, 0 ≤ M i j)
    (hrow : ∀ i, (∑ j, M i j) ≤ S) (hcol : ∀ j, (∑ i, M i j) ≤ S)
    (hx : ∀ i, |x i| ≤ a) (hy : ∀ j, |y j| ≤ a)
    (hraw : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := I m) ((1-P m)*M*(1-P m))‖ ≤ q)
    (hNrow : ∀ i, (∑ j, expScaled M x y i j) = 1)
    (hNcol : ∀ j, (∑ i, expScaled M x y i j) = 1) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I m) (realComplex (expScaled M x y-P m))‖ ≤
      q+S*(Real.exp (2*a)-1) := by
  have hbase := realComplex_gap ((1-P m)*M*(1-P m)) hq hraw
  have hdiff := ScalingOperatorPerturbation.complex_operator_bound M x y ha hS hM hrow hcol hx hy
  rw [centered_decomposition hm M (expScaled M x y) hNrow hNcol,
    realComplex_add, map_add]
  exact (norm_add_le _ _).trans (add_le_add hbase
    ((compressed_norm hm (expScaled M x y-M)).trans hdiff))

theorem actual_scaled_fixed_gap (hm : 0 < m)
    (M : Matrix (I m) (I m) ℝ) (x y : I m → ℝ) {a S q q' : ℝ}
    (ha : 0 ≤ a) (hS : 0 ≤ S) (hq : 0 ≤ q)
    (hM : ∀ i j, 0 ≤ M i j)
    (hrow : ∀ i, (∑ j, M i j) ≤ S) (hcol : ∀ j, (∑ i, M i j) ≤ S)
    (hx : ∀ i, |x i| ≤ a) (hy : ∀ j, |y j| ≤ a)
    (hraw : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := I m) ((1-P m)*M*(1-P m))‖ ≤ q)
    (hNrow : ∀ i, (∑ j, expScaled M x y i j) = 1)
    (hNcol : ∀ j, (∑ i, expScaled M x y i j) = 1)
    (hbudget : q+S*(Real.exp (2*a)-1) ≤ q') (hq' : q' < 1) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I m) (realComplex (expScaled M x y-P m))‖ ≤ q' ∧ q' < 1 :=
  ⟨(actual_scaled_centered_gap hm M x y ha hS hq hM hrow hcol hx hy hraw hNrow hNcol).trans hbudget, hq'⟩
end ScalingCenteredGap
#print axioms ScalingCenteredGap.projection_data
#print axioms ScalingCenteredGap.doubly_stochastic_centering
#print axioms ScalingCenteredGap.actual_scaled_centered_gap
