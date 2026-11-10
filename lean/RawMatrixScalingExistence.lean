import ActualScalingContraction
import ActualHessianComplex
import RealGaugeOperator

/-! Verified in the 557-module direct-Lean compilation and declaration audit.
Raw-matrix adapter. Its assumptions are raw nonnegative entries,
density, marginal residuals, the real centered gap, and two explicit smallness
conditions. Linear inverse and gauge/Hessian compatibility are derived below. -/
set_option autoImplicit false
noncomputable section
namespace RawMatrixScalingExistence
open Matrix Finset ActualMarginalRemainder RealGaugeSolution RealGaugeOperator
open scoped Matrix.Norms.L2Operator
variable {m : ℕ}

def realQ (M : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ :=
  Matrix.fromBlocks 0 (ActualHessianFinite.centered M)
    (ActualHessianFinite.centered M).transpose 0

def rawK (C q : ℝ) : ℝ := 2*BalancedHessianInverse.inverseConstant (C+4) q

lemma cast_realQ (M : Matrix (Fin m) (Fin m) ℝ) :
    complexify (realQ M) = ActualHessianComplex.Q M := by
  ext i j
  cases i <;> cases j <;>
    simp [complexify, realQ, ActualHessianComplex.Q, ActualHessianComplex.B,
      ActualHessianComplex.realComplex, BipartiteOperatorBound.block,
      Matrix.conjTranspose_apply, Matrix.transpose_apply]

lemma real_model_eq (hm : 0 < m) (M : Matrix (Fin m) (Fin m) ℝ) :
    realModel (realQ M) = ActualHessianFinite.model M := by
  have hh : complexify (realModel (realQ M)) =
      ActualHessianComplex.realComplex (ActualHessianFinite.model M) := by
    rw [complexify_model, cast_realQ, ActualHessianComplex.cast_model hm]
  ext i j
  have hij := congrArg (fun A => (A i j).re) hh
  simpa [complexify, ActualHessianComplex.realComplex] using hij

lemma map_add (A B : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ) :
    realInfinityMap (A+B) = realInfinityMap A + realInfinityMap B := by
  ext z i
  change ((A+B)*ᵥz) i = (A*ᵥz) i + (B*ᵥz) i
  rw [Matrix.add_mulVec]; rfl
lemma map_mul (A B : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ) :
    realInfinityMap (A*B) = realInfinityMap A * realInfinityMap B := by
  ext z i
  change ((A*B)*ᵥz) i = (A*ᵥ(B*ᵥz)) i
  rw [Matrix.mulVec_mulVec]
lemma map_one : realInfinityMap (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ) = 1 := by
  ext z i
  change (1 *ᵥ z) i = z i
  rw [Matrix.one_mulVec]

/-- The actual finite derivative equals the independently defined block Hessian. -/
lemma hessian_eq (M : Matrix (Fin m) (Fin m) ℝ) :
    hessian M = realInfinityMap (ActualHessianFinite.actual M) := by
  ext z k
  cases k <;>
    simp [hessian_apply, linearPart, edge, realInfinityMap_apply,
      ActualHessianFinite.actual, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type, Matrix.diagonal_apply, Matrix.transpose_apply,
      ActualHessianFinite.row, ActualHessianFinite.col, mul_add,
      sum_add_distrib, ← sum_mul, ← mul_sum, eq_comm] <;> ring

lemma gauge_kernel (hm : 0 < m) (z : V m) :
    realInfinityMap (realGauge m) z = 0 ↔ signedMass z = 0 := by
  rw [realInfinityMap_apply, realGauge_kernel_iff hm]
  exact sub_eq_zero.symm

lemma forcing_bound (M : Matrix (Fin m) (Fin m) ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hr : ∀ i, |ActualHessianFinite.r M i| ≤ ε)
    (hc : ∀ j, |ActualHessianFinite.c M j| ≤ ε) :
    ‖marginals M 0‖ ≤ ε := by
  apply (pi_norm_le_iff_of_nonneg hε).mpr
  intro k
  cases k with
  | inl i => simpa [marginals, edge, ActualHessianFinite.r, ActualHessianFinite.row,
      Real.norm_eq_abs] using hr i
  | inr j => simpa [marginals, edge, ActualHessianFinite.c, ActualHessianFinite.col,
      Real.norm_eq_abs] using hc j

/-- Raw-M endpoint. Neither a scaling nor an inverse/gauge identity is a premise.
The radius is 2Kε; both explicit smallness restrictions remain visible. -/
theorem exists_scaling (hm : 0 < m) (M : Matrix (Fin m) (Fin m) ℝ)
    {C ε q : ℝ} (hC : 0 ≤ C) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hM : ∀ i j, 0 ≤ M i j) (hd : ∀ i j, M i j ≤ C/(m : ℝ))
    (hr : ∀ i, |ActualHessianFinite.r M i| ≤ ε)
    (hc : ∀ j, |ActualHessianFinite.c M j| ≤ ε)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hgap : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin m) ((1-ActualHessianFinite.P m)*M*(1-ActualHessianFinite.P m))‖ ≤ q)
    (hinv : BalancedHessianInverse.inverseConstant (C+4) q*(4*ε) ≤ 1/2)
    (hcontract : rawK C q*(2*(1+ε)*(Real.exp (4*rawK C q*ε)-1)) ≤ 1/2) :
    ∃ z : V m, ‖z‖ ≤ 2*rawK C q*ε ∧ signedMass z = 0 ∧
      (∀ i, (∑ j, M i j*Real.exp (edge z i j)) = 1) ∧
      (∀ j, (∑ i, M i j*Real.exp (edge z i j)) = 1) := by
  let Q := realQ M
  let E := ActualHessianFinite.perturbation M
  let J := realModel Q+E+realGauge m
  let L := realInfinityMap J⁻¹
  let G := realInfinityMap (realGauge m)
  have hQgap : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin m ⊕ Fin m) (complexify Q)‖ ≤ q := by
    simpa only [Q, cast_realQ] using ActualHessianComplex.Q_gap hm M hq0 hgap
  have hQdensity : ∀ i j, ‖Q i j‖ ≤ (C+4)/(m:ℝ) := by
    intro i j
    have hh := ActualHessianComplex.Q_density hm M hC hM hd hε1 hr hc i j
    rw [← cast_realQ] at hh
    simpa [Q, complexify] using hh
  have hQbal : BalancedHessianInverse.Balanced (complexify Q) := by
    simpa only [Q, cast_realQ] using ActualHessianComplex.Q_balanced hm M
  have hErow : ∀ i, (∑ j, ‖E i j‖) ≤ 4*ε := by
    intro i
    simpa only [E, Real.norm_eq_abs] using
      ActualHessianFinite.perturbation_row_bound hm M hr hc i
  have hGE : BalancedHessianInverse.gauge m * complexify E = 0 := by
    exact ActualHessianComplex.E_gauge hm M
  have hi := real_inverse_matrix hm Q E (by linarith : 0 ≤ C+4)
    (by positivity : 0 ≤ 4*ε) hQgap hq1 hQdensity hQbal hErow hGE hinv
  change J⁻¹*J=1 ∧ J*J⁻¹=1 ∧ ‖L‖≤rawK C q ∧ realGauge m*J⁻¹=realGauge m at hi
  have hK : 0 ≤ rawK C q := (norm_nonneg L).trans hi.2.2.1
  have hJ : J = ActualHessianFinite.actual M + realGauge m := by
    dsimp [J, Q, E]
    rw [real_model_eq hm, ← ActualHessianFinite.actual_eq_model_add]
  have hJL : (hessian M+G)*L=1 := by
    rw [hessian_eq]
    change (realInfinityMap (ActualHessianFinite.actual M)+
      realInfinityMap (realGauge m))*realInfinityMap J⁻¹=1
    rw [← map_add, ← hJ, ← map_mul, hi.2.1, map_one]
  have hGL : G*L=G := by
    change realInfinityMap (realGauge m)*realInfinityMap J⁻¹=realInfinityMap (realGauge m)
    rw [← map_mul, hi.2.2.2]
  have hrows : ∀ i, (∑ j, M i j) ≤ 1+ε := by
    intro i
    have hh := (abs_le.mp (hr i)).2
    dsimp [ActualHessianFinite.r, ActualHessianFinite.row] at hh
    linarith
  have hcols : ∀ j, (∑ i, M i j) ≤ 1+ε := by
    intro j
    have hh := (abs_le.mp (hc j)).2
    dsimp [ActualHessianFinite.c, ActualHessianFinite.col] at hh
    linarith
  apply ActualScalingContraction.exists_actual_scaling M G L
    (a := 2*rawK C q*ε) (S := 1+ε) (K := rawK C q)
    (by positivity) (by positivity) hK hM hrows hcols
    (gauge_kernel hm) hi.2.2.1 hJL hGL
  · simpa only [show 2*(2*rawK C q*ε) = 4*rawK C q*ε by ring] using hcontract
  · have hh := mul_le_mul_of_nonneg_left (forcing_bound M hε0 hr hc) hK
    nlinarith

end RawMatrixScalingExistence
#print axioms RawMatrixScalingExistence.hessian_eq
#print axioms RawMatrixScalingExistence.exists_scaling
