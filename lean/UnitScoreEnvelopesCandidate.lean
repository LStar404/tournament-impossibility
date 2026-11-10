import UnitScorePrefactorCandidate
import ActualTournamentDisplacementCandidate
set_option autoImplicit false
noncomputable section
namespace UnitScoreEnvelopesCandidate
open Matrix Finset TournamentHamiltonian ActualTournamentPrescalingBounds
open ActualPrescalingNormalization TournamentPrescalingMassBound
open DeletedScalingSynthesisCandidate
variable {n : ℕ}

lemma unit_score_caps (T : Tournament n) (hn : 4≤n)
    (hs : ∀ i, |score T i|≤1) :
    (∀ i, |normalizedScore T i|≤2/(n:ℝ)) ∧
    (∀ i, |normalizedScore T i|≤1/2) ∧
    tau (normalizedScore T)≤4/(n:ℝ) ∧ tau (normalizedScore T)≤1 := by
  have hnR : (4:ℝ)≤n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by linarith
  have hd : 0<(n:ℝ)-1 := by linarith
  have ha : ∀ i, |normalizedScore T i|≤2/(n:ℝ) := by
    intro i
    unfold normalizedScore
    rw [abs_div, abs_of_pos hd]
    apply (div_le_div_of_nonneg_right (hs i) hd.le).trans
    apply (div_le_div_iff₀ hd hn0).mpr
    linarith
  have hb : (2:ℝ)/(n:ℝ)≤1/2 := (div_le_iff₀ hn0).mpr (by linarith)
  have ht : tau (normalizedScore T)≤4/(n:ℝ) := by
    calc
      _ ≤ ∑ i : Fin n, (2/(n:ℝ))^2 := by
        apply Finset.sum_le_sum
        intro i hi
        have hh := ha i
        nlinarith [sq_abs (normalizedScore T i), abs_nonneg (normalizedScore T i)]
      _ = _ := by simp; field_simp; ring
  refine ⟨ha, fun i => (ha i).trans hb, ht, ?_⟩
  exact ht.trans ((div_le_iff₀ hn0).mpr (by linarith))

lemma unit_sqrt_ratio (T : Tournament n) (hn : 4≤n)
    (hs : ∀ i, |score T i|≤1) :
    Real.sqrt (tau (normalizedScore T))/Real.sqrt (n:ℝ)≤2/(n:ℝ) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hs0 : 0<Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr hnR
  have ht := (unit_score_caps T hn hs).2.2.1
  have hh := Real.sqrt_le_sqrt ht
  rw [Real.sqrt_div (by norm_num : (0:ℝ)≤4), show Real.sqrt (4:ℝ)=2 by norm_num] at hh
  calc
    _ ≤ (2/Real.sqrt (n:ℝ))/Real.sqrt (n:ℝ) := div_le_div_of_nonneg_right hh hs0.le
    _ = _ := by rw [div_div, ← pow_two, Real.sq_sqrt hnR.le]

lemma unit_mass_delta (T : Tournament n) (hn : 4≤n)
    (hs : ∀ i, |score T i|≤1) :
    massBound T (1/2)≤32/(n:ℝ) ∧ normalizedMarginalBound T (1/2)≤200/(n:ℝ) := by
  have hnR : (4:ℝ)≤n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by linarith
  have ht0 := tau_nonneg (normalizedScore T)
  have ht1 := (unit_score_caps T hn hs).2.2.2
  have hr := unit_sqrt_ratio T hn hs
  have he : errorScale n (tau (normalizedScore T))≤4/(n:ℝ) := by
    have h1 : (tau (normalizedScore T)+tau (normalizedScore T)^2)/(n:ℝ)≤2/(n:ℝ) :=
      div_le_div_of_nonneg_right (by nlinarith) hn0.le
    have h2 := mul_le_mul_of_nonneg_left hr ht0
    have h3 := mul_le_mul_of_nonneg_right ht1 (show 0≤2/(n:ℝ) by positivity)
    unfold errorScale
    simp only [mul_div_assoc] at *
    simp only [div_eq_mul_inv] at h1 h2 h3 ⊢
    nlinarith only [h1,h2,h3]
  have hmass : massBound T (1/2)≤32/(n:ℝ) := by
    unfold massBound radiusFactor
    norm_num
    have hh := mul_le_mul_of_nonneg_left he (by norm_num : (0:ℝ)≤64/9)
    simp only [div_eq_mul_inv] at hh ⊢
    nlinarith [inv_nonneg.mpr hn0.le]
  refine ⟨hmass,?_⟩
  unfold normalizedMarginalBound scaleCap
  norm_num
  have hm := div_le_div_of_nonneg_right hmass hn0.le
  have hinv : (1:ℝ)/(n:ℝ)≤1/4 := (div_le_iff₀ hn0).mpr (by linarith)
  have hinv0 : (0:ℝ)≤(n:ℝ)⁻¹ := inv_nonneg.mpr hn0.le
  simp only [div_eq_mul_inv] at hr hm hinv ⊢
  nlinarith

lemma unit_deletion_budgets (T : Tournament n) (hn : 4≤n)
    (hs : ∀ i, |score T i|≤1) (I : Finset (Fin n)) (m : ℕ)
    (hhalf : (I.card:ℝ)≤(n:ℝ)/2)
    (hgap : (n:ℝ)/2≤(m:ℝ)-actualK T (1/2) I) :
    actualK T (1/2) I≤930*((I.card:ℝ)+1)^2/(n:ℝ) ∧
    residualBudget n m I.card (16*(scaleCap (1/2))^2)
      (normalizedMarginalBound T (1/2)) (actualK T (1/2) I)≤1460*((I.card:ℝ)+1)/(n:ℝ) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have ht0 : (0:ℝ)≤I.card := Nat.cast_nonneg _
  have hd := (unit_mass_delta T hn hs).2
  have hk := NormalizationScalarsCandidate.K_budget hnR ht0 hhalf
    (show 0≤16*(scaleCap (1/2))^2 by positivity)
    (normalizedMarginalBound_nonneg T (1/2)) (show actualK T (1/2) I=_ from rfl)
  have he := (NormalizationScalarsCandidate.epsilon_budget hnR ht0
    (show 0≤16*(scaleCap (1/2))^2 by positivity)
    (normalizedMarginalBound_nonneg T (1/2)) hk.1 hgap hk.2).2
  have hdm := mul_le_mul_of_nonneg_left hd (show 0≤4*(I.card:ℝ) by positivity)
  constructor
  · unfold actualK scaleCap
    norm_num
    simp only [div_eq_mul_inv] at hdm ⊢
    have hi : (0:ℝ)≤(n:ℝ)⁻¹ := inv_nonneg.mpr hnR.le
    nlinarith [mul_nonneg hi (sq_nonneg (I.card:ℝ)), mul_nonneg hi ht0]
  · change residualBudget n m I.card (16*(scaleCap (1/2))^2)
      (normalizedMarginalBound T (1/2)) (actualK T (1/2) I)≤_ at he
    norm_num [scaleCap] at he ⊢
    simp only [div_eq_mul_inv] at he hd ⊢
    have hi : (0:ℝ)≤(n:ℝ)⁻¹ := inv_nonneg.mpr hnR.le
    nlinarith [mul_nonneg hi ht0]
end UnitScoreEnvelopesCandidate
