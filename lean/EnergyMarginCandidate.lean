import Mathlib
/-! Verified finite scalar margin. Conditional finite scalar margin only. -/
set_option autoImplicit false
noncomputable section
namespace EnergyMarginCandidate

/-- A half-denominator gate turns comparison with a decaying upper bound into
an explicit energy bound. No claim that U equals the reference constant L. -/
lemma energy_margin {L U n C Cref t h rho : ℝ}
    (hL : 0 < L) (hU : 0 < U) (hn : 0 < n)
    (hC : 0 ≤ C) (hCref : 0 ≤ Cref)
    (hsmall : (C+Cref)/n ≤ L/2)
    (hlower : L-Cref/n ≤ h)
    (hupper : h ≤ rho*Real.exp (-t/2)+C/n)
    (hrho : rho ≤ U) :
    t ≤ 2*Real.log (U/L)+4*(C+Cref)/(L*n) := by
  let d := (C+Cref)/n
  have hd0 : 0 ≤ d := by dsimp [d]; positivity
  have hdsmall : d ≤ L/2 := hsmall
  have hden : 0 < L-d := by linarith
  have hmid : L-d ≤ U*Real.exp (-t/2) := by
    have hr := mul_le_mul_of_nonneg_right hrho (Real.exp_pos (-t/2)).le
    dsimp [d]
    have he : (C+Cref)/n=C/n+Cref/n := by ring
    linarith
  have he : (L-d)/U ≤ Real.exp (-t/2) := (div_le_iff₀ hU).mpr (by simpa only [mul_comm] using hmid)
  have hlog := Real.log_le_log (div_pos hden hU) he
  rw [Real.log_exp, Real.log_div hden.ne' hU.ne'] at hlog
  have hratio : L/(L-d) ≤ 1+2*d/L := by
    apply (div_le_iff₀ hden).mpr
    have hfrac : 0 ≤ d/L := div_nonneg hd0 hL.le
    have hm := mul_nonneg hfrac (show 0 ≤ L-2*d by linarith)
    have heq : (1+2*d/L)*(L-d)-L = d/L*(L-2*d) := by field_simp; ring
    linarith
  have hlogratio := Real.log_le_sub_one_of_pos (div_pos hL hden)
  rw [Real.log_div hL.ne' hden.ne'] at hlogratio
  have hlogs : Real.log L-Real.log (L-d) ≤ 2*d/L := by linarith
  rw [Real.log_div hU.ne' hL.ne']
  have heq : 4*(C+Cref)/(L*n)=4*d/L := by dsimp [d]; ring
  rw [heq]
  simp only [div_eq_mul_inv] at hlog hlogs ⊢
  linarith
end EnergyMarginCandidate
