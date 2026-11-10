import RawScalingThreshold
import ActualRootCoercivity
import ScalingDensityFrobenius
import ScalingCenteredGap

/-! Focused compiled synthesis. Every conclusion uses the SAME root supplied
by RawScalingThreshold. No centered-block gap, inverse, or root is assumed.
This local scaling endpoint is not the full original impossibility theorem. -/
set_option autoImplicit false
noncomputable section
namespace RawScalingSynthesis
open Matrix Finset WithLp
open ActualHessianFinite ActualHessianComplex MatrixScalingMassPotential
open FiniteSymmetricQuadratic ActualRootEnergy
open scoped Matrix.Norms.L2Operator
variable {m : ℕ}

lemma cast_l2_norm {α : Type*} [Fintype α] (v : α → ℝ) :
    ‖(toLp 2 (fun i => (v i : ℂ)) : EuclideanSpace ℂ α)‖ =
      ‖(toLp 2 v : EuclideanSpace ℝ α)‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [EuclideanSpace.norm_sq_eq, Complex.norm_real]

/-- Restriction to real vectors proves the reverse spectral comparison. -/
lemma real_gap_of_complex {α : Type*} [Fintype α] [DecidableEq α]
    (A : Matrix α α ℝ) {q : ℝ} (hq : 0 ≤ q)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (realComplex A)‖ ≤ q) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ ≤ q := by
  apply ContinuousLinearMap.opNorm_le_bound _ hq
  intro z
  have hh := (Matrix.toEuclideanCLM (𝕜 := ℂ) (realComplex A)).le_opNorm
    (toLp 2 (fun i => (ofLp z i : ℂ)))
  have hmul : realComplex A *ᵥ (fun i => (ofLp z i : ℂ)) =
      fun i => ((A *ᵥ ofLp z) i : ℂ) := by
    ext i
    simp [realComplex, Matrix.mulVec, dotProduct]
  have hh' := hh.trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
  change ‖toLp 2 (realComplex A *ᵥ (fun i => (ofLp z i : ℂ)))‖ ≤
    q*‖toLp 2 (fun i => (ofLp z i : ℂ))‖ at hh'
  rw [hmul, cast_l2_norm, cast_l2_norm] at hh'
  change ‖(toLp 2 (A *ᵥ ofLp z) : EuclideanSpace ℝ α)‖ ≤ q*‖z‖
  simpa using hh'

lemma raw_centered_block_gap (hm : 0 < m) (M : Matrix (Fin m) (Fin m) ℝ)
    {q : ℝ} (hq : 0 ≤ q)
    (hraw : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin m)
      ((1-P m)*M*(1-P m))‖ ≤ q) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (ActualRootCoercivity.centeredBlock M)‖ ≤ q := by
  apply real_gap_of_complex _ hq
  have hc : realComplex (ActualRootCoercivity.centeredBlock M) = Q M := by
    ext i j
    cases i <;> cases j <;>
      simp [realComplex, ActualRootCoercivity.centeredBlock, Q, B,
        BipartiteOperatorBound.block, Matrix.conjTranspose_apply, Matrix.transpose_apply]
  rw [hc]
  exact Q_gap hm M hq hraw

/-- Depends only on C and q and also leaves a positive coercivity denominator. -/
def epsilonThreshold (C q : ℝ) :=
  min (RawScalingThreshold.epsilonThreshold C q) ((1-q)/8)

def radius (C q ε : ℝ) := 2*RawMatrixScalingExistence.rawK C q*ε

lemma epsilonThreshold_pos {C q : ℝ} (hC : 0 ≤ C) (hq : q < 1) :
    0 < epsilonThreshold C q := by
  exact lt_min (RawScalingThreshold.epsilonThreshold_pos hC hq) (by positivity)

/-- Exact inverse constant expansion yields a large gap-weighted lower bound. -/
lemma rawK_gap_product {C q : ℝ} (hC : 0 ≤ C) (hq : q < 1) :
    128 ≤ RawMatrixScalingExistence.rawK C q * (1-q) := by
  have hden : 0 < 1-q := sub_pos.mpr hq
  have hexpand : RawMatrixScalingExistence.rawK C q * (1-q) =
      (3+4*(C+4))*(1-q)+8*(C+4)^2 := by
    unfold RawMatrixScalingExistence.rawK BalancedHessianInverse.inverseConstant
      DenseResolventRowBound.rowConstant DenseResolventRowBound.entryConstant
    field_simp [ne_of_gt hden]
    ring
  rw [hexpand]
  have hp : 0 ≤ (3+4*(C+4))*(1-q) := mul_nonneg (by linarith) hden.le
  nlinarith [sq_nonneg C]

/-- The existing epsilon threshold already preserves a fixed spectral gap.
The sharper increment budget is (1-q)/512, so the midpoint bound is generous. -/
lemma spectral_increment_bound {C q ε : ℝ} (hC : 0 ≤ C) (hq : q < 1)
    (hε0 : 0 ≤ ε) (hε : ε ≤ RawScalingThreshold.epsilonThreshold C q) :
    (1+ε)*(Real.exp (2*radius C q ε)-1) ≤ (1-q)/512 ∧
      q+(1+ε)*(Real.exp (2*radius C q ε)-1) ≤ (1+q)/2 := by
  have hK : 0 < RawMatrixScalingExistence.rawK C q := by
    unfold RawMatrixScalingExistence.rawK
    exact mul_pos (by norm_num) (ScalingEpsilonThreshold.inverse_constant_pos hC hq)
  have hs := ScalingEpsilonThreshold.smallness hK
    (show RawMatrixScalingExistence.rawK C q =
      2*BalancedHessianInverse.inverseConstant (C+4) q from rfl) hε0 hε
  have hbudget : RawMatrixScalingExistence.rawK C q *
      ((1+ε)*(Real.exp (2*radius C q ε)-1)) ≤ 1/4 := by
    have ht : 2*radius C q ε = 4*RawMatrixScalingExistence.rawK C q*ε := by
      unfold radius
      ring
    rw [ht]
    nlinarith [hs.2.2]
  have hp := rawK_gap_product hC hq
  have hsharp : (1+ε)*(Real.exp (2*radius C q ε)-1) ≤ (1-q)/512 := by
    apply (mul_le_mul_iff_right₀ hK).mp
    nlinarith [hbudget, hp]
  exact ⟨hsharp, by linarith⟩

/-- One raw-matrix endpoint: same-root normalization, infinity and Euclidean
control, density, residual-energy Frobenius bound, and explicit centered gap.
The same epsilon threshold also guarantees the fixed centered gap (1+q)/2<1. -/
theorem exists_controlled_scaling (hm : 0 < m) (M : Matrix (Fin m) (Fin m) ℝ)
    {C ε q : ℝ} (hC : 0 ≤ C) (hε0 : 0 ≤ ε)
    (hε : ε ≤ epsilonThreshold C q)
    (hM : ∀ i j, 0 ≤ M i j) (hd : ∀ i j, M i j ≤ C/(m : ℝ))
    (hr : ∀ i, |r M i| ≤ ε) (hc : ∀ j, |c M j| ≤ ε)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hraw : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin m)
      ((1-P m)*M*(1-P m))‖ ≤ q) :
    let a := radius C q ε
    ∃ x y : Fin m → ℝ,
      ‖vector x y‖ ≤ a ∧
      (∑ i, x i) = ∑ j, y j ∧
      root M x y ∧
      l2 (vector x y) ≤ Real.exp (2*a)/(1-q-4*ε) * l2 (ActualRootEnergy.residual M) ∧
      (∀ i j, 0 ≤ expScaled M x y i j ∧
        expScaled M x y i j ≤ Real.exp (2*a)*(C/(m : ℝ))) ∧
      (∑ i, ∑ j, (expScaled M x y i j-M i j)^2) ≤
        (2*C*(1+ε)*Real.exp (4*a)/(m : ℝ)) *
          (Real.exp (2*a)/(1-q-4*ε))^2 * energy (ActualRootEnergy.residual M) ∧
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (realComplex (expScaled M x y-P m))‖ ≤
        q+(1+ε)*(Real.exp (2*a)-1) ∧
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (realComplex (expScaled M x y-P m))‖ ≤
        (1+q)/2 ∧ (1+q)/2 < 1 := by
  let a := radius C q ε
  have hεroot : ε ≤ RawScalingThreshold.epsilonThreshold C q :=
    hε.trans (min_le_left _ _)
  have hεgap : ε ≤ (1-q)/8 := hε.trans (min_le_right _ _)
  have hgap : 4*ε < 1-q := by linarith
  have hden : 0 < 1-q-4*ε := by linarith
  obtain ⟨z, hz, hbal, hrows, hcols⟩ := RawScalingThreshold.exists_scaling
    hm M hC hε0 hεroot hM hd hr hc hq0 hq1 hraw
  let x : Fin m → ℝ := fun i => z (Sum.inl i)
  let y : Fin m → ℝ := fun j => z (Sum.inr j)
  have hv : vector x y = z := by ext i; cases i <;> rfl
  have ha : 0 ≤ a := by
    have hK := ScalingEpsilonThreshold.inverse_constant_pos hC hq1
    dsimp [a, radius, RawMatrixScalingExistence.rawK]
    positivity
  have hz' : ‖vector x y‖ ≤ a := by simpa [hv, a, radius] using hz
  have hx : ∀ i, |x i| ≤ a := by
    intro i
    have hp : |x i| ≤ ‖z‖ := by
      simpa [Real.norm_eq_abs, x] using norm_le_pi_norm z (Sum.inl i)
    exact hp.trans hz
  have hy : ∀ j, |y j| ≤ a := by
    intro j
    have hp : |y j| ≤ ‖z‖ := by
      simpa [Real.norm_eq_abs, y] using norm_le_pi_norm z (Sum.inr j)
    exact hp.trans hz
  have hxy : (∑ i, x i) = ∑ j, y j := by
    exact sub_eq_zero.mp hbal
  have hroot : root M x y := by
    exact ⟨hrows, hcols⟩
  have hNrows : ∀ i, (∑ j, expScaled M x y i j) = 1 := hroot.1
  have hNcols : ∀ j, (∑ i, expScaled M x y i j) = 1 := hroot.2
  have hrow : ∀ i, (∑ j, M i j) ≤ 1+ε := by
    intro i
    have hh := (abs_le.mp (hr i)).2
    dsimp [r, ActualHessianFinite.row] at hh
    linarith
  have hcol : ∀ j, (∑ i, M i j) ≤ 1+ε := by
    intro j
    have hh := (abs_le.mp (hc j)).2
    dsimp [c, ActualHessianFinite.col] at hh
    linarith
  have hL2 := ActualRootCoercivity.actual_root_l2 hm M x y ha hq0 hgap hM
    (raw_centered_block_gap hm M hq0 hraw) hr hc hx hy hxy hroot
  have henergy : energy (vector x y) ≤
      (Real.exp (2*a)/(1-q-4*ε))^2 * energy (ActualRootEnergy.residual M) := by
    have hcoef : 0 ≤ Real.exp (2*a)/(1-q-4*ε) := by positivity
    have hh := (sq_le_sq₀ (Real.sqrt_nonneg _)
      (mul_nonneg hcoef (Real.sqrt_nonneg _))).mpr hL2
    simpa only [mul_pow, Real.sq_sqrt (energy_nonneg _)] using hh
  have hF := ScalingDensityFrobenius.frobenius_energy_fin hm M x y ha hC
    hM hd hrow hcol hx hy
  have hsum : (∑ i, (x i)^2)+(∑ j, (y j)^2) = energy (vector x y) := by
    simp [energy, vector, Fintype.sum_sum_type]
  rw [hsum] at hF
  have hFcoef : 0 ≤ 2*C*(1+ε)*Real.exp (4*a)/(m : ℝ) := by positivity
  refine ⟨x, y, hz', hxy, hroot, hL2, ?_, ?_, ?_⟩
  · exact ScalingDensityFrobenius.scaled_density M x y hM hd hx hy
  · exact hF.trans (by simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left henergy hFcoef)
  · have hg := ScalingCenteredGap.actual_scaled_centered_gap hm M x y ha (by positivity)
      hq0 hM hrow hcol hx hy hraw hNrows hNcols
    have hb := (spectral_increment_bound hC hq1 hε0 hεroot).2
    exact ⟨hg, hg.trans hb, by linarith⟩

end RawScalingSynthesis
#print axioms RawScalingSynthesis.raw_centered_block_gap
#print axioms RawScalingSynthesis.epsilonThreshold_pos
#print axioms RawScalingSynthesis.rawK_gap_product
#print axioms RawScalingSynthesis.spectral_increment_bound
#print axioms RawScalingSynthesis.exists_controlled_scaling
