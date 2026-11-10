import ActualHessianFinite

/-! Verified in the 557-module direct-Lean compilation and declaration audit. Adapter for the actual Hessian.
All error and balance conclusions below are derived from actual M.
The only spectral input is the REAL operator norm of (I-P) M (I-P). -/
set_option autoImplicit false
noncomputable section
namespace ActualHessianComplex
open Matrix Finset WithLp
open ActualHessianFinite
open scoped Matrix.Norms.L2Operator

variable {m : ℕ}
def realComplex {α β : Type*} (A : Matrix α β ℝ) : Matrix α β ℂ :=
  fun i j => (A i j : ℂ)

@[simp] theorem realComplex_add {α β : Type*} (A B : Matrix α β ℝ) :
    realComplex (A+B) = realComplex A + realComplex B := by
  ext i j
  simp [realComplex]
@[simp] theorem realComplex_zero {α β : Type*} :
    realComplex (0 : Matrix α β ℝ) = 0 := by
  ext i j
  simp [realComplex]
@[simp] theorem realComplex_mul {α β γ : Type*} [Fintype β]
    (A : Matrix α β ℝ) (B : Matrix β γ ℝ) :
    realComplex (A*B) = realComplex A * realComplex B := by
  ext i j
  simp [realComplex, Matrix.mul_apply]

/-- A real Euclidean operator bound also holds after complexification.
No skew symmetry, normality, or supplied complex spectral gap is required. -/
theorem realComplex_gap {α : Type*} [Fintype α] [DecidableEq α]
    (A : Matrix α α ℝ) {q : ℝ} (hq : 0 ≤ q)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ ≤ q) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (realComplex A)‖ ≤ q := by
  have hb (v : α → ℝ) : ‖toLp 2 (A *ᵥ v)‖ ≤ q * ‖toLp 2 v‖ := by
    have hh := (Matrix.toEuclideanCLM (𝕜 := ℝ) A).le_opNorm (toLp 2 v)
    exact hh.trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
  apply ContinuousLinearMap.opNorm_le_bound _ hq
  intro z
  let xr : α → ℝ := fun i => (ofLp z i).re
  let xi : α → ℝ := fun i => (ofLp z i).im
  have hr := sq_le_sq₀ (norm_nonneg (toLp 2 (A *ᵥ xr)))
    (mul_nonneg hq (norm_nonneg (toLp 2 xr))) |>.mpr (hb xr)
  have hi := sq_le_sq₀ (norm_nonneg (toLp 2 (A *ᵥ xi)))
    (mul_nonneg hq (norm_nonneg (toLp 2 xi))) |>.mpr (hb xi)
  have hre (i : α) : ((realComplex A *ᵥ ofLp z) i).re = (A *ᵥ xr) i := by
    simp [realComplex, Matrix.mulVec, dotProduct, Complex.mul_re, xr]
  have him (i : α) : ((realComplex A *ᵥ ofLp z) i).im = (A *ᵥ xi) i := by
    simp [realComplex, Matrix.mulVec, dotProduct, Complex.mul_im, xi]
  have hz : ‖z‖^2 = ‖toLp 2 xr‖^2 + ‖toLp 2 xi‖^2 := by
    simp [EuclideanSpace.norm_sq_eq, Complex.sq_norm, Complex.normSq_apply,
      xr, xi, ← sq, Finset.sum_add_distrib]
  have hAz : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (realComplex A) z‖^2 =
      ‖toLp 2 (A *ᵥ xr)‖^2 + ‖toLp 2 (A *ᵥ xi)‖^2 := by
    simp only [EuclideanSpace.norm_sq_eq, Matrix.ofLp_toEuclideanCLM,
      Complex.sq_norm, Complex.normSq_apply, ← sq, hre, him,
      Finset.sum_add_distrib, ofLp_toLp, Real.norm_eq_abs, sq_abs]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hq (norm_nonneg z))).mp
  rw [hAz, mul_pow, hz]
  nlinarith

def B (M : Matrix (I m) (I m) ℝ) := realComplex (centered M)
def Q (M : Matrix (I m) (I m) ℝ) := BipartiteOperatorBound.block (B M) (B M)ᴴ
def E (M : Matrix (I m) (I m) ℝ) := realComplex (perturbation M)
def H (M : Matrix (I m) (I m) ℝ) := realComplex (actual M)

theorem B_rows (hm : 0 < m) (M : Matrix (I m) (I m) ℝ) (i : I m) :
    ∑ j, B M i j = 0 := by
  have hh := congrArg (fun x : ℝ => (x : ℂ)) (centered_row hm M i)
  simpa [B, realComplex] using hh

theorem B_cols (hm : 0 < m) (M : Matrix (I m) (I m) ℝ) (j : I m) :
    ∑ i, B M i j = 0 := by
  have hh := congrArg (fun x : ℝ => (x : ℂ)) (centered_col hm M j)
  simpa [B, realComplex] using hh

/-- All four projector annihilation identities, not an assumed balance package. -/
theorem Q_balanced (hm : 0 < m) (M : Matrix (I m) (I m) ℝ) :
    BalancedHessianInverse.Balanced (Q M) :=
  BalancedHessianInverse.centered_block_balanced (B M) (B_rows hm M) (B_cols hm M)

theorem Q_gap (hm : 0 < m) (M : Matrix (I m) (I m) ℝ) {q : ℝ}
    (hq : 0 ≤ q)
    (hraw : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := I m) ((1-P m)*M*(1-P m))‖ ≤ q) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (Q M)‖ ≤ q := by
  apply BalancedHessianInverse.centered_block_gap (B M) hq
  apply realComplex_gap (centered M) hq
  simpa only [centered_projection hm M] using hraw

theorem Q_density (hm : 0 < m) (M : Matrix (I m) (I m) ℝ) {C ε : ℝ}
    (hC : 0 ≤ C) (hM : ∀ i j, 0 ≤ M i j)
    (hd : ∀ i j, M i j ≤ C/(m : ℝ)) (hε : ε ≤ 1)
    (hr : ∀ i, |r M i| ≤ ε) (hc : ∀ j, |c M j| ≤ ε)
    (i j : Block m) : ‖Q M i j‖ ≤ (C+4)/(m : ℝ) := by
  have hb := centered_density hm M hM hd hε hr hc
  have hn : 0 ≤ (C+4)/(m : ℝ) := by positivity
  rcases i with i | i <;> rcases j with j | j
  · simpa [Q, BipartiteOperatorBound.block] using hn
  · simpa [Q, BipartiteOperatorBound.block, B, realComplex, Real.norm_eq_abs] using hb i j
  · simpa [Q, BipartiteOperatorBound.block, B, realComplex,
      Matrix.conjTranspose_apply, Real.norm_eq_abs] using hb j i
  · simpa [Q, BipartiteOperatorBound.block] using hn

theorem cast_gauge : realComplex (ActualHessianFinite.gauge m) =
    BalancedHessianInverse.gauge m := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  all_goals simp [realComplex, ActualHessianFinite.gauge, ActualHessianFinite.sign,
    BalancedHessianInverse.gauge, BalancedHessianInverse.sign]

theorem E_gauge (hm : 0 < m) (M : Matrix (I m) (I m) ℝ) :
    BalancedHessianInverse.gauge m * E M = 0 := by
  have hh := congrArg realComplex (gauge_perturbation hm M)
  simpa only [realComplex_mul, cast_gauge, realComplex_zero, E] using hh

theorem E_rows (hm : 0 < m) (M : Matrix (I m) (I m) ℝ) {ε : ℝ}
    (hr : ∀ i, |r M i| ≤ ε) (hc : ∀ j, |c M j| ≤ ε) (i : Block m) :
    (∑ j, ‖E M i j‖) ≤ 4*ε := by
  simpa [E, realComplex, Real.norm_eq_abs] using perturbation_row_bound hm M hr hc i

/-- Explicit same-side zero / opposite-side 1/m projector calculation. -/
theorem cast_model (hm : 0 < m) (M : Matrix (I m) (I m) ℝ) :
    realComplex (ActualHessianFinite.model M) = BalancedHessianInverse.model (Q M) := by
  have hn : (m : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  ext i j
  rcases i with i | i <;> rcases j with j | j
  all_goals simp [realComplex, ActualHessianFinite.model, Q, B, P,
    BipartiteOperatorBound.block, BalancedHessianInverse.model,
    BalancedHessianInverse.plus, BalancedHessianInverse.gauge,
    BalancedHessianInverse.sign, Matrix.one_apply, Matrix.conjTranspose_apply,
    Matrix.transpose_apply]
  all_goals try { split_ifs }
  all_goals try field_simp
  all_goals ring
  all_goals split_ifs <;> norm_num

theorem H_eq_model_add (hm : 0 < m) (M : Matrix (I m) (I m) ℝ) :
    H M = BalancedHessianInverse.model (Q M) + E M := by
  unfold H
  rw [actual_eq_model_add, realComplex_add, cast_model hm]
  rfl

/-- Actual-M endpoint. No error-row, balance, inverse, or invertibility conclusion
is included among the inputs. This is a complex solution; real extraction and
uniform linear-operator construction belong to the separate sibling adapter. -/
theorem actual_complex_solution (hm : 0 < m) (M : Matrix (I m) (I m) ℝ)
    {C ε q : ℝ} (hC : 0 ≤ C) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hM : ∀ i j, 0 ≤ M i j) (hd : ∀ i j, M i j ≤ C/(m : ℝ))
    (hr : ∀ i, |r M i| ≤ ε) (hc : ∀ j, |c M j| ≤ ε)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hraw : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := I m) ((1-P m)*M*(1-P m))‖ ≤ q)
    (hsmall : BalancedHessianInverse.inverseConstant (C+4) q * (4*ε) ≤ 1/2)
    (w : Block m → ℂ) (hw : BalancedHessianInverse.gauge m *ᵥ w = 0) :
    ∃ z : Block m → ℂ, BalancedHessianInverse.gauge m *ᵥ z = 0 ∧
      H M *ᵥ z = w ∧ ‖z‖ ≤ 2*BalancedHessianInverse.inverseConstant (C+4) q*‖w‖ := by
  have hh := BalancedHessianInverse.perturbed_gauge_solution hm (Q M) (E M)
    (by linarith : 0 ≤ C+4) (by positivity : 0 ≤ 4*ε)
    (Q_gap hm M hq0 hraw) hq1 (Q_density hm M hC hM hd hε1 hr hc)
    (Q_balanced hm M) (E_rows hm M hr hc) (E_gauge hm M) hsmall w hw
  simpa only [← H_eq_model_add hm M] using hh

end ActualHessianComplex
#print axioms ActualHessianComplex.realComplex_gap
#print axioms ActualHessianComplex.cast_model
#print axioms ActualHessianComplex.actual_complex_solution
