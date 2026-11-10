import DeletedScalingSynthesisCandidate

/-! Verified in the 557-module direct-Lean compilation and declaration audit.
Finite uniform gate for remaining logarithmic-window budgets. -/
set_option autoImplicit false
noncomputable section
namespace LogWindowScalarGateCandidate
open DeletedScalingSynthesisCandidate

lemma rawK_mono {C D q r : ℝ} (hC : 0 ≤ C) (hCD : C ≤ D)
    (hqr : q ≤ r) (hr : r < 1) :
    RawMatrixScalingExistence.rawK C q ≤ RawMatrixScalingExistence.rawK D r := by
  unfold RawMatrixScalingExistence.rawK BalancedHessianInverse.inverseConstant
    DenseResolventRowBound.rowConstant DenseResolventRowBound.entryConstant
  have hq : 0 < 1-q := by linarith
  have hr' : 0 < 1-r := by linarith
  gcongr

lemma threshold_antitone {C D q r : ℝ} (hC : 0 ≤ C) (hCD : C ≤ D)
    (hqr : q ≤ r) (hr : r < 1) :
    RawScalingSynthesis.epsilonThreshold D r ≤ RawScalingSynthesis.epsilonThreshold C q := by
  have hk := rawK_mono hC hCD hqr hr
  have hk0 : 0 < RawMatrixScalingExistence.rawK C q := by
    unfold RawMatrixScalingExistence.rawK
    exact mul_pos (by norm_num) (ScalingEpsilonThreshold.inverse_constant_pos hC (by linarith))
  have hdk0 := hk0.trans_le hk
  unfold RawScalingSynthesis.epsilonThreshold RawScalingThreshold.epsilonThreshold ScalingEpsilonThreshold.threshold
  apply min_le_min
  · apply min_le_min le_rfl
    apply min_le_min
    · apply one_div_le_one_div_of_le (by positivity) (by gcongr)
    · apply one_div_le_one_div_of_le (by positivity) (by gcongr)
  · linarith

/-- Pure numerical gate. q is the fixed pre-deletion gap; u,v,d are
uniform upper budgets for t/n,K/n,delta respectively. -/
theorem scalar_gate {n m : ℕ} {t C δ K q u v d : ℝ}
    (hn : 0 < n) (hm : (m:ℝ)=(n:ℝ)-t)
    (ht : 0 ≤ t) (hC : 0 ≤ C) (_hδ : 0 ≤ δ) (_hK : 0 ≤ K)
    (hq0 : 0 ≤ q) (hq : q < 1) (hu : 0 ≤ u) (hv : 0 ≤ v) (hd : 0 ≤ d)
    (htu : t/(n:ℝ) ≤ u) (hKv : K/(n:ℝ) ≤ v) (hδd : δ ≤ d)
    (hz : u+v ≤ (1-q)/2)
    (hε : 2*(d+(C+1)*u+v) ≤ RawScalingSynthesis.epsilonThreshold (2*C) ((1+q)/2)) :
    K < (m:ℝ) ∧ gapBudget n m q K < 1 ∧
      residualBudget n m t C δ K ≤
        RawScalingSynthesis.epsilonThreshold (density m C K) (gapBudget n m q K) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have ht' := (div_le_iff₀ hnR).mp htu
  have hK' := (div_le_iff₀ hnR).mp hKv
  have hz' := mul_le_mul_of_nonneg_left hz hnR.le
  have hden : (n:ℝ)/2 ≤ (m:ℝ)-K := by nlinarith
  have hden0 : 0 < (m:ℝ)-K := by linarith
  have hsmall : K < (m:ℝ) := by linarith
  have hm0 : 0 ≤ (m:ℝ) := by positivity
  have hqbar : (1+q)/2 < 1 := by linarith
  have hgap : gapBudget n m q K ≤ (1+q)/2 := by
    unfold gapBudget
    apply (div_le_iff₀ hden0).mpr
    have hsq := mul_nonneg hnR.le (sq_nonneg (1-q))
    have hpos := mul_le_mul_of_nonneg_left
      (show (n:ℝ)*(1+q)/2 ≤ (m:ℝ)-K by nlinarith) (show 0 ≤ (1+q)/2 by positivity)
    nlinarith
  have hdensity : density m C K ≤ 2*C := by
    unfold density
    apply (div_le_iff₀ hden0).mpr
    have hh := mul_le_mul_of_nonneg_left hden hC
    have hh2 := mul_le_mul_of_nonneg_left (show (m:ℝ) ≤ n by linarith) hC
    nlinarith
  have hC' : 0 ≤ density m C K := by unfold density; positivity
  have hres : residualBudget n m t C δ K ≤ 2*(d+(C+1)*u+v) := by
    unfold residualBudget
    apply (div_le_iff₀ hden0).mpr
    have hh1 := mul_le_mul_of_nonneg_left hδd hnR.le
    have hh2 := mul_le_mul_of_nonneg_left ht' (show 0 ≤ C+1 by positivity)
    have hh3 := mul_le_mul_of_nonneg_left hden (show 0 ≤ 2*(d+(C+1)*u+v) by positivity)
    nlinarith
  exact ⟨hsmall,hgap.trans_lt hqbar,
    hres.trans (hε.trans (threshold_antitone hC' hdensity hgap hqbar))⟩
end LogWindowScalarGateCandidate
