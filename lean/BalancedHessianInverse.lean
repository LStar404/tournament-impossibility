import DenseResolventRowBound
import BipartiteOperatorBound

/-!
Focused compiled candidate. Canonical gauge correction and a small-perturbation inverse.
The hypotheses are a genuine Euclidean gap, entry density, exact balance
identities, and an entrywise row-sum perturbation bound. No inverse norm or
scaling-existence conclusion is assumed. The nonlinear scaling problem remains.
-/
noncomputable section
namespace BalancedHessianInverse
open Matrix Finset DenseResolventRowBound
open scoped Matrix.Norms.L2Operator
variable {m : ℕ}

def plus (m : ℕ) : Matrix (Block m) (Block m) ℂ :=
  fun _ _ => (2*(m : ℂ))⁻¹

def sign (m : ℕ) : Block m → ℂ := Sum.elim (fun _ => 1) (fun _ => -1)

def gauge (m : ℕ) : Matrix (Block m) (Block m) ℂ :=
  fun i j => (2*(m : ℂ))⁻¹ * sign m i * sign m j

def Balanced (Q : Matrix (Block m) (Block m) ℂ) : Prop :=
  Q * plus m = 0 ∧ plus m * Q = 0 ∧ Q * gauge m = 0 ∧ gauge m * Q = 0

def model (Q : Matrix (Block m) (Block m) ℂ) := 1 + Q + plus m - gauge m

def baseline (Q : Matrix (Block m) (Block m) ℂ) := 1 + Q + plus m

def baseInverse (Q : Matrix (Block m) (Block m) ℂ) :=
  resolvent Q - (1/2 : ℂ) • plus m

def inverseConstant (C q : ℝ) := rowConstant C q + 1/2

lemma plus_square (hm : 0 < m) : plus m * plus m = plus m := by
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  ext i j
  simp only [plus, Matrix.mul_apply, sum_const, card_univ,
    Fintype.card_sum, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp [hmC]
  ring

lemma gauge_square (hm : 0 < m) : gauge m * gauge m = gauge m := by
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  ext i j
  cases i <;> cases j <;>
    simp [gauge, sign, Matrix.mul_apply, Fintype.sum_sum_type] <;>
    field_simp [hmC] <;> ring

lemma plus_gauge : plus m * gauge m = 0 := by
  ext i j
  cases j <;> simp [plus, gauge, sign, Matrix.mul_apply, Fintype.sum_sum_type] <;> ring

lemma gauge_plus : gauge m * plus m = 0 := by
  ext i j
  cases i <;> simp [plus, gauge, sign, Matrix.mul_apply, Fintype.sum_sum_type] <;> ring

/-- The projector kernel is exactly the usual equal-sums gauge. -/
lemma gauge_mulVec_formula (w : Block m → ℂ) (i : Block m) :
    (gauge m *ᵥ w) i = (2*(m : ℂ))⁻¹ * sign m i *
      ((∑ k, w (Sum.inl k)) - ∑ k, w (Sum.inr k)) := by
  cases i <;>
    simp [gauge, sign, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      mul_sub, mul_sum, mul_assoc] <;> ring

lemma gauge_kernel_iff (hm : 0 < m) (w : Block m → ℂ) :
    gauge m *ᵥ w = 0 ↔ (∑ k, w (Sum.inl k)) = ∑ k, w (Sum.inr k) := by
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hc : (2*(m : ℂ))⁻¹ ≠ 0 := inv_ne_zero (mul_ne_zero (by norm_num) hmC)
  constructor
  · intro hw
    have hi := congrArg (fun v : Block m → ℂ => v (Sum.inl ⟨0, hm⟩)) hw
    change (gauge m *ᵥ w) (Sum.inl ⟨0, hm⟩) = 0 at hi
    rw [gauge_mulVec_formula] at hi
    simp only [sign, Sum.elim_inl, mul_one] at hi
    exact sub_eq_zero.mp ((mul_eq_zero.mp hi).resolve_left hc)
  · intro hw
    ext i
    rw [gauge_mulVec_formula, hw, sub_self, mul_zero]
    rfl

lemma plus_row_sum (hm : 0 < m) (i : Block m) : (∑ j, ‖plus m i j‖) = 1 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  simp [plus, norm_inv, norm_mul, Complex.norm_natCast, Fintype.sum_sum_type]
  field_simp [hmR.ne']
  norm_num

/-- The exact balanced block equations follow from B's row and column sums. -/
lemma centered_block_balanced (B : Matrix (Fin m) (Fin m) ℂ)
    (hr : ∀ i, (∑ j, B i j) = 0) (hc : ∀ j, (∑ i, B i j) = 0) :
    Balanced (BipartiteOperatorBound.block B Bᴴ) := by
  have hrH (i : Fin m) : (∑ j, Bᴴ i j) = 0 := by
    simpa [Matrix.conjTranspose_apply] using congrArg star (hc i)
  have hcH (j : Fin m) : (∑ i, Bᴴ i j) = 0 := by
    simpa [Matrix.conjTranspose_apply] using congrArg star (hr j)
  unfold Balanced
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    ext i j
    cases i <;> cases j <;>
      simp [BipartiteOperatorBound.block, plus, gauge, sign, Matrix.mul_apply,
        Matrix.fromBlocks, Fintype.sum_sum_type, ← sum_mul, ← mul_sum,
        hr, hc, hrH, hcH, ← map_sum]

lemma centered_block_gap (B : Matrix (Fin m) (Fin m) ℂ) {q : ℝ} (hq : 0 ≤ q)
    (hB : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) B‖ ≤ q) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (BipartiteOperatorBound.block B Bᴴ)‖ ≤ q := by
  apply BipartiteOperatorBound.bound _ _ q hq hB
  simpa only [Matrix.l2_opNorm_toEuclideanCLM, Matrix.l2_opNorm_conjTranspose] using hB

/-- Correcting only the plus projection inverts H0+Pminus, not H0 itself. -/
theorem base_inverse_data (hm : 0 < m) (Q : Matrix (Block m) (Block m) ℂ)
    {q : ℝ} (hQ : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) Q‖ ≤ q) (hq : q < 1)
    (hb : Balanced Q) :
    baseInverse Q * baseline Q = 1 ∧ baseline Q * baseInverse Q = 1 := by
  have hd := inverse_data Q hQ hq
  have hAP : (1+Q)*plus m = plus m := by rw [add_mul, one_mul, hb.1, add_zero]
  have hPA : plus m*(1+Q) = plus m := by rw [mul_add, mul_one, hb.2.1, add_zero]
  have hRP : resolvent Q * plus m = plus m := by
    calc
      _ = resolvent Q * ((1+Q)*plus m) := by rw [hAP]
      _ = (resolvent Q*(1+Q))*plus m := by rw [mul_assoc]
      _ = _ := by rw [hd.1, one_mul]
  have hPR : plus m * resolvent Q = plus m := by
    calc
      _ = (plus m*(1+Q))*resolvent Q := by rw [hPA]
      _ = plus m*((1+Q)*resolvent Q) := by rw [mul_assoc]
      _ = _ := by rw [hd.2.1, mul_one]
  constructor
  · unfold baseInverse baseline
    rw [sub_mul, mul_add, hd.1, hRP, smul_mul, mul_add, hPA, plus_square hm]
    module
  · unfold baseInverse baseline
    rw [mul_sub, add_mul, hd.2.1, hPR, Matrix.mul_smul, add_mul, hAP, plus_square hm]
    module

lemma model_gauge_left (hm : 0 < m) (Q : Matrix (Block m) (Block m) ℂ)
    (hb : Balanced Q) : gauge m * model Q = 0 := by
  unfold model
  rw [mul_sub, mul_add, mul_add, mul_one, hb.2.2.2, gauge_plus, gauge_square hm]
  abel

/-- K is obtained from the genuine resolvent row bound and canonical Pplus. -/
theorem base_inverse_infinity_bound (hm : 0 < m) (Q : Matrix (Block m) (Block m) ℂ)
    {C q : ℝ} (hC : 0 ≤ C)
    (hQ : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) Q‖ ≤ q) (hq : q < 1)
    (he : ∀ i j, ‖Q i j‖ ≤ C/(m : ℝ)) :
    ‖infinityMap (baseInverse Q)‖ ≤ inverseConstant C q := by
  have hD := entryConstant_nonneg hC hq
  apply infinityMap_norm_le _ (by unfold inverseConstant rowConstant; positivity)
  intro i
  calc
    _ ≤ ∑ j, (‖resolvent Q i j‖ + (1/2 : ℝ)*‖plus m i j‖) := by
      apply sum_le_sum
      intro j hj
      have h := norm_sub_le (resolvent Q i j) ((1/2 : ℂ)*plus m i j)
      simpa [baseInverse, Matrix.sub_apply, Matrix.smul_apply, norm_mul] using h
    _ = (∑ j, ‖resolvent Q i j‖) + (1/2 : ℝ) := by
      rw [sum_add_distrib, ← mul_sum, plus_row_sum hm, mul_one]
    _ ≤ _ := add_le_add (inverse_row_bound hm Q hC hQ hq he i) le_rfl

/-- Construct a genuine inverse on the gauge kernel after a small row-sum
perturbation. Neither the inverse nor its desired bound is supplied by callers.
This is a linear theorem; it does not assert existence of nonlinear scaling. -/
theorem perturbed_gauge_solution (hm : 0 < m)
    (Q E : Matrix (Block m) (Block m) ℂ) {C q d : ℝ}
    (hC : 0 ≤ C) (hd : 0 ≤ d)
    (hQ : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) Q‖ ≤ q) (hq : q < 1)
    (he : ∀ i j, ‖Q i j‖ ≤ C/(m : ℝ)) (hb : Balanced Q)
    (hE : ∀ i, (∑ j, ‖E i j‖) ≤ d) (hGE : gauge m * E = 0)
    (hsmall : inverseConstant C q * d ≤ 1/2)
    (w : Block m → ℂ) (hw : gauge m *ᵥ w = 0) :
    ∃ z : Block m → ℂ, gauge m *ᵥ z = 0 ∧ (model Q+E) *ᵥ z = w ∧
      ‖z‖ ≤ 2 * inverseConstant C q * ‖w‖ := by
  let A := infinityMap (baseline Q)
  let L := infinityMap (baseInverse Q)
  let D := infinityMap E
  let F := L * D
  let N := neumann F
  let T := N * L
  have hi := base_inverse_data hm Q hQ hq hb
  have hAL : A*L = 1 := by
    change infinityMap (baseline Q) * infinityMap (baseInverse Q) = 1
    rw [← infinityMap_mul, hi.2, infinityMap_one]
  have hLA : L*A = 1 := by
    change infinityMap (baseInverse Q) * infinityMap (baseline Q) = 1
    rw [← infinityMap_mul, hi.1, infinityMap_one]
  have hK : 0 ≤ inverseConstant C q := by
    have hnon := entryConstant_nonneg hC hq
    unfold inverseConstant rowConstant
    positivity
  have hL : ‖L‖ ≤ inverseConstant C q := base_inverse_infinity_bound hm Q hC hQ hq he
  have hD : ‖D‖ ≤ d := infinityMap_norm_le E hd hE
  have hF : ‖F‖ ≤ inverseConstant C q*d :=
    (norm_mul_le L D).trans (mul_le_mul hL hD (norm_nonneg D) hK)
  have hn := neumann_data F hF (by linarith : inverseConstant C q*d < 1)
  have hN : ‖N‖ ≤ 2 := by
    apply hn.2.2.trans
    apply (div_le_iff₀ (by linarith : 0 < 1-inverseConstant C q*d)).mpr
    linarith
  have hfactor : A+D = A*(1+F) := by
    change A+D = A*(1+L*D)
    rw [mul_add, mul_one, ← mul_assoc, hAL, one_mul]
  have hJT : (A+D)*T = 1 := by
    change (A+D)*(N*L) = 1
    rw [hfactor, mul_assoc, ← mul_assoc (1+F) N L, hn.1, one_mul, hAL]
  have hT : ‖T‖ ≤ 2*inverseConstant C q :=
    (norm_mul_le N L).trans (mul_le_mul hN hL (norm_nonneg L) (by norm_num))
  let z := T w
  have hJz : (model Q+E+gauge m) *ᵥ z = w := by
    have hmats : model Q+E+gauge m = baseline Q+E := by
      unfold model baseline
      abel
    have hc := congrArg (fun f : (Block m → ℂ) →L[ℂ] (Block m → ℂ) => f w) hJT
    simpa [hmats, infinityMap_add, Matrix.add_mulVec, A, D, z] using hc
  have hGJ : gauge m*(model Q+E+gauge m) = gauge m := by
    rw [mul_add, mul_add, model_gauge_left hm Q hb, hGE, gauge_square hm]
    simp
  have hGz : gauge m *ᵥ z = 0 := by
    calc
      _ = (gauge m*(model Q+E+gauge m)) *ᵥ z := by rw [hGJ]
      _ = gauge m *ᵥ ((model Q+E+gauge m) *ᵥ z) := by rw [Matrix.mulVec_mulVec]
      _ = 0 := by rw [hJz, hw]
  refine ⟨z, hGz, ?_, ?_⟩
  · have h := hJz
    rw [Matrix.add_mulVec, hGz, add_zero] at h
    exact h
  · exact (T.le_opNorm w).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg w))

end BalancedHessianInverse
#print axioms BalancedHessianInverse.gauge_kernel_iff
#print axioms BalancedHessianInverse.centered_block_balanced
#print axioms BalancedHessianInverse.base_inverse_data
#print axioms BalancedHessianInverse.base_inverse_infinity_bound
#print axioms BalancedHessianInverse.perturbed_gauge_solution
