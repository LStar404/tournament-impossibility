import BalancedHessianInverse

/-! Explicit positive epsilon threshold depending only on the linear inverse
constant. Prepared without compilation while another worker owns the window. -/
set_option autoImplicit false
noncomputable section
namespace ScalingEpsilonThreshold

def threshold (K : ℝ) : ℝ := min 1 (min (1 / (8*K)) (1 / (64*K^2)))

lemma threshold_pos {K : ℝ} (hK : 0 < K) : 0 < threshold K := by
  unfold threshold
  positivity

lemma exp_sub_one_le {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.exp t - 1 ≤ 2*t := by
  have hden : 0 < 2-t := by linarith
  have hexp := Real.exp_le_two_add_div_two_sub ht (by linarith : t < 2)
  have ht2 : t^2 ≤ t := by nlinarith
  have hfrac : (2+t)/(2-t) ≤ 1+2*t := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  linarith

/-- A single explicit threshold ensures both Neumann and contraction smallness. -/
theorem smallness {β K ε : ℝ} (hK : 0 < K) (hrel : K = 2*β)
    (hε0 : 0 ≤ ε) (hε : ε ≤ threshold K) :
    ε ≤ 1 ∧ β*(4*ε) ≤ 1/2 ∧
      K*(2*(1+ε)*(Real.exp (4*K*ε)-1)) ≤ 1/2 := by
  have hε1 : ε ≤ 1 := hε.trans (min_le_left _ _)
  have hε8 : ε ≤ 1/(8*K) := hε.trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hε64 : ε ≤ 1/(64*K^2) := hε.trans
    ((min_le_right _ _).trans (min_le_right _ _))
  have h8 : ε*(8*K) ≤ 1 := (le_div_iff₀ (by positivity : 0 < 8*K)).mp hε8
  have h64 : ε*(64*K^2) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < 64*K^2)).mp hε64
  have ht0 : 0 ≤ 4*K*ε := by positivity
  have ht1 : 4*K*ε ≤ 1 := by nlinarith
  have hexp : Real.exp (4*K*ε)-1 ≤ 8*K*ε := by
    nlinarith [exp_sub_one_le ht0 ht1]
  have hfac : 0 ≤ K*(2*(1+ε)) := by positivity
  have hprod := mul_le_mul_of_nonneg_left hexp hfac
  have hεfactor : K*(2*(1+ε))*(8*K*ε) ≤ 32*K^2*ε := by
    have hh := mul_le_mul_of_nonneg_left hε1 (by positivity : 0 ≤ 16*K^2*ε)
    nlinarith
  refine ⟨hε1, ?_, ?_⟩
  · nlinarith [h8]
  · calc
      K*(2*(1+ε)*(Real.exp (4*K*ε)-1))
          = (K*(2*(1+ε)))*(Real.exp (4*K*ε)-1) := by ring
      _ ≤ K*(2*(1+ε))*(8*K*ε) := hprod
      _ ≤ 32*K^2*ε := hεfactor
      _ ≤ 1/2 := by nlinarith [h64]

lemma inverse_constant_pos {C q : ℝ} (hC : 0 ≤ C) (hq : q < 1) :
    0 < BalancedHessianInverse.inverseConstant (C+4) q := by
  have he := DenseResolventRowBound.entryConstant_nonneg
    (by linarith : 0 ≤ C+4) hq
  unfold BalancedHessianInverse.inverseConstant DenseResolventRowBound.rowConstant
  linarith

end ScalingEpsilonThreshold
#print axioms ScalingEpsilonThreshold.threshold_pos
#print axioms ScalingEpsilonThreshold.exp_sub_one_le
#print axioms ScalingEpsilonThreshold.smallness
#print axioms ScalingEpsilonThreshold.inverse_constant_pos
