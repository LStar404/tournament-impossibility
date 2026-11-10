import BalancedHessianInverse

/-! Real-valued specialization of the constructed complex BalancedHessianInverse.gauge inverse.
This is a linear theorem only. No nonlinear scaling existence is claimed. -/
set_option autoImplicit false
noncomputable section
namespace RealGaugeSolution
open Matrix Finset DenseResolventRowBound BalancedHessianInverse
variable {m : ℕ}

def complexify (A : Matrix (Block m) (Block m) ℝ) : Matrix (Block m) (Block m) ℂ :=
  fun i j => (A i j : ℂ)

def realPlus (m : ℕ) : Matrix (Block m) (Block m) ℝ :=
  fun _ _ => (2 * (m : ℝ))⁻¹

def realSign (m : ℕ) : Block m → ℝ := Sum.elim (fun _ => 1) (fun _ => -1)

def realGauge (m : ℕ) : Matrix (Block m) (Block m) ℝ :=
  fun i j => (2 * (m : ℝ))⁻¹ * realSign m i * realSign m j

def realModel (Q : Matrix (Block m) (Block m) ℝ) :=
  1 + Q + realPlus m - realGauge m

lemma realGauge_mulVec_formula (w : Block m → ℝ) (i : Block m) :
    (realGauge m *ᵥ w) i = (2*(m : ℝ))⁻¹ * realSign m i *
      ((∑ k, w (Sum.inl k)) - ∑ k, w (Sum.inr k)) := by
  cases i <;>
    simp [realGauge, realSign, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      mul_sub, mul_sum, mul_assoc] <;> ring

lemma realGauge_kernel_iff (hm : 0 < m) (w : Block m → ℝ) :
    realGauge m *ᵥ w = 0 ↔ (∑ k, w (Sum.inl k)) = ∑ k, w (Sum.inr k) := by
  have hmC : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hc : (2*(m : ℝ))⁻¹ ≠ 0 := inv_ne_zero (mul_ne_zero (by norm_num) hmC)
  constructor
  · intro hw
    have hi := congrArg (fun v : Block m → ℝ => v (Sum.inl ⟨0, hm⟩)) hw
    change (realGauge m *ᵥ w) (Sum.inl ⟨0, hm⟩) = 0 at hi
    rw [realGauge_mulVec_formula] at hi
    simp only [realSign, Sum.elim_inl, mul_one] at hi
    exact sub_eq_zero.mp ((mul_eq_zero.mp hi).resolve_left hc)
  · intro hw
    ext i
    rw [realGauge_mulVec_formula, hw, sub_self, mul_zero]
    rfl

lemma complexify_model (Q : Matrix (Block m) (Block m) ℝ) :
    complexify (realModel Q) = model (complexify Q) := by
  ext i j
  cases i <;> cases j <;>
    simp [complexify, realModel, model, realPlus, plus, realGauge, BalancedHessianInverse.gauge,
      realSign, sign, Matrix.one_apply] <;> split_ifs <;> simp_all

lemma realPart_mulVec (A : Matrix (Block m) (Block m) ℝ) (z : Block m → ℂ) :
    A *ᵥ (fun i => (z i).re) = fun i => (((complexify A) *ᵥ z) i).re := by
  ext i
  simp [Matrix.mulVec, dotProduct, complexify, Complex.mul_re]

lemma norm_realPart_le (z : Block m → ℂ) : ‖fun i => (z i).re‖ ≤ ‖z‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg z)).mpr
  intro i
  have h : ‖(z i).re‖ ≤ ‖z i‖ := by
    simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm (z i)
  exact h.trans (norm_le_pi_norm z i)

lemma norm_complexify_vec (w : Block m → ℝ) : ‖fun i => (w i : ℂ)‖ = ‖w‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg w)).mpr
    intro i
    simpa only [Complex.norm_real] using norm_le_pi_norm w i
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (fun i => (w i : ℂ)))).mpr
    intro i
    simpa only [Complex.norm_real] using norm_le_pi_norm (fun i => (w i : ℂ)) i

/-- Real input matrices and RHS admit a real BalancedHessianInverse.gauge-kernel solution, with exactly
    the complex theorem's dimension-free sup-norm constant. -/
theorem perturbed_real_gauge_solution (hm : 0 < m)
    (Q E : Matrix (Block m) (Block m) ℝ) {C q d : ℝ}
    (hC : 0 ≤ C) (hd : 0 ≤ d)
    (hQ : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (complexify Q)‖ ≤ q) (hq : q < 1)
    (he : ∀ i j, ‖Q i j‖ ≤ C / (m : ℝ)) (hb : Balanced (complexify Q))
    (hE : ∀ i, (∑ j, ‖E i j‖) ≤ d)
    (hGE : BalancedHessianInverse.gauge m * complexify E = 0)
    (hsmall : inverseConstant C q * d ≤ 1/2)
    (w : Block m → ℝ) (hw : (∑ k, w (Sum.inl k)) = ∑ k, w (Sum.inr k)) :
    ∃ z : Block m → ℝ,
      (∑ k, z (Sum.inl k)) = ∑ k, z (Sum.inr k) ∧
      realGauge m *ᵥ z = 0 ∧
      (realModel Q + E) *ᵥ z = w ∧
      ‖z‖ ≤ 2 * inverseConstant C q * ‖w‖ := by
  have hwC : BalancedHessianInverse.gauge m *ᵥ (fun i => (w i : ℂ)) = 0 := by
    apply (gauge_kernel_iff hm _).mpr
    exact_mod_cast hw
  have heC : ∀ i j, ‖complexify Q i j‖ ≤ C / (m : ℝ) := by
    simpa only [complexify, Complex.norm_real] using he
  have hEC : ∀ i, (∑ j, ‖complexify E i j‖) ≤ d := by
    simpa only [complexify, Complex.norm_real] using hE
  obtain ⟨v, hvg, hv, hvn⟩ := perturbed_gauge_solution hm (complexify Q)
    (complexify E) hC hd hQ hq heC hb hEC hGE hsmall (fun i => (w i : ℂ)) hwC
  have hvs := (gauge_kernel_iff hm v).mp hvg
  have hrs : (∑ k, (v (Sum.inl k)).re) = ∑ k, (v (Sum.inr k)).re := by
    simpa using congrArg Complex.re hvs
  refine ⟨fun i => (v i).re, hrs, ?_, ?_, ?_⟩
  · exact (realGauge_kernel_iff hm _).mpr hrs
  · rw [realPart_mulVec]
    have hc : complexify (realModel Q + E) = model (complexify Q) + complexify E := by
      rw [← complexify_model]
      ext i j
      simp [complexify]
    rw [hc, hv]
    simp
  · exact (norm_realPart_le v).trans (by simpa only [norm_complexify_vec] using hvn)

end RealGaugeSolution
#print axioms RealGaugeSolution.perturbed_real_gauge_solution
