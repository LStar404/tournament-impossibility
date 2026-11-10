import ActualUnitScorePrefactorCandidate
set_option autoImplicit false
noncomputable section
namespace MinorNormalizationCandidate
open UnitScorePrefactorCandidate PhysicalMinorRecoveryCandidate

lemma referenceScale_base (n m : ℕ) (hn : 0<n) (hm : 0 < m) :
    referenceScale n m*base m=((m.factorial:ℝ)/(2:ℝ)^m)*(1-1/(n:ℝ))^m := by
  have hm0 : (m:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hm
  unfold referenceScale base
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  have he : (m:ℝ)*((n:ℝ)-1)/(2*(n:ℝ))=(m:ℝ)/2*(1-1/(n:ℝ)) := by field_simp
  rw [he, mul_pow, div_pow]
  field_simp

lemma deletion_scalar_bounds {n m : ℕ} (hn : 2≤n) (hm : m≤n) :
    Real.exp (-1-2/(n:ℝ))≤(1-1/(n:ℝ))^m ∧ (1-1/(n:ℝ))^m≤1 := by
  have hnR : (2:ℝ)≤n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by linarith
  have hd : 0<(n:ℝ)-1 := by linarith
  have hx : 0<1-1/(n:ℝ) := by apply sub_pos.mpr; exact (div_lt_one hn0).mpr (by linarith)
  have hlo := Real.one_sub_inv_le_log_of_pos hx
  have he : 1-(1-1/(n:ℝ))⁻¹= -1/((n:ℝ)-1) := by field_simp; ring
  rw [he] at hlo
  have hmR : (m:ℝ)≤n := by exact_mod_cast hm
  have hl : -1-2/(n:ℝ)≤(m:ℝ)*Real.log (1-1/(n:ℝ)) := by
    have hh := mul_le_mul_of_nonneg_left hlo (Nat.cast_nonneg m)
    have hmn : (m:ℝ)/((n:ℝ)-1)≤(n:ℝ)/((n:ℝ)-1) := div_le_div_of_nonneg_right hmR hd.le
    have hr : (n:ℝ)/((n:ℝ)-1)≤1+2/(n:ℝ) := by
      apply (div_le_iff₀ hd).mpr
      field_simp
      nlinarith
    simp only [div_eq_mul_inv] at hh hmn hr ⊢
    linarith
  constructor
  · rw [← Real.exp_log (pow_pos hx m), Real.log_pow]
    exact Real.exp_le_exp.mpr hl
  · exact pow_le_one₀ hx.le (by linarith [div_pos (show (0:ℝ)<1 by norm_num) hn0])
end MinorNormalizationCandidate
