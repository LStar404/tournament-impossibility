import LogWindowErrorCandidate
import LogWindowScalarGateCandidate

/-! Verified in the 557-module direct-Lean compilation and declaration audit.
Uniform logarithmic-window completion for numerical budgets. -/
set_option autoImplicit false
noncomputable section
namespace LogWindowDeletionBudgetCandidate
open Filter
open scoped Topology
open TournamentHamiltonian ActualTournamentPrescalingBounds ActualPrescalingNormalization
open TournamentPrescalingMassBound ActualNormalizedCenteredGapCandidate
open LogWindowErrorCandidate LogWindowScalarGateCandidate DeletedScalingSynthesisCandidate

def deltaEnvelope (A a0 : ℝ) (n : ℕ) : ℝ :=
  16*(scaleCap a0)^2*Real.sqrt (A*Real.log (n:ℝ)/(n:ℝ))+
    4*actualMassEnvelope A a0 n/(n:ℝ)
def deletionRatio (B : ℝ) (n : ℕ) : ℝ := B*Real.log (n:ℝ)/(n:ℝ)
def kappaRatio (A B a0 : ℝ) (n : ℕ) : ℝ :=
  4*deletionRatio B n*deltaEnvelope A a0 n+
    2*(16*(scaleCap a0)^2+1)*(deletionRatio B n)^2

def totalRatio (A B a0 : ℝ) (n : ℕ) := deletionRatio B n+kappaRatio A B a0 n
def epsilonEnvelope (A B a0 : ℝ) (n : ℕ) :=
  2*(deltaEnvelope A a0 n+(16*(scaleCap a0)^2+1)*deletionRatio B n+kappaRatio A B a0 n)

lemma nat_log_nonneg (n : ℕ) : 0 ≤ Real.log (n:ℝ) := by
  by_cases hn : n=0
  · simp [hn]
  · apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ n by omega)

lemma massEnvelope_nonneg {A : ℝ} (hA : 0 ≤ A) (n : ℕ) : 0 ≤ massEnvelope A n := by
  have hl := nat_log_nonneg n
  unfold massEnvelope
  positivity

lemma deltaEnvelope_nonneg {A a0 : ℝ} (hA : 0 ≤ A) (n : ℕ) : 0 ≤ deltaEnvelope A a0 n := by
  have hm := massEnvelope_nonneg hA n
  unfold deltaEnvelope actualMassEnvelope
  positivity

lemma deletionRatio_nonneg {B : ℝ} (hB : 0 ≤ B) (n : ℕ) : 0 ≤ deletionRatio B n := by
  have hl := nat_log_nonneg n
  unfold deletionRatio
  positivity

lemma kappaRatio_nonneg {A B a0 : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (n : ℕ) :
    0 ≤ kappaRatio A B a0 n := by
  have hd := deltaEnvelope_nonneg (a0:=a0) hA n
  have ht := deletionRatio_nonneg hB n
  unfold kappaRatio
  positivity

lemma deltaEnvelope_tendsto (A a0 : ℝ) : Tendsto (deltaEnvelope A a0) atTop (𝓝 0) := by
  have hl : Tendsto (fun n : ℕ => A*Real.log (n:ℝ)/(n:ℝ)) atTop (𝓝 0) := by
    have hh : Tendsto (fun n : ℕ => Real.log (n:ℝ)/(n:ℝ)) atTop (𝓝 0) := by
      simpa using log_power_decay 1 (by norm_num : (0:ℝ)<1)
    simpa only [mul_zero, mul_div_assoc] using hh.const_mul A
  have hs := (Real.continuous_sqrt.tendsto 0).comp hl
  have hm : Tendsto (actualMassEnvelope A a0) atTop (𝓝 0) := by
    change Tendsto (fun n : ℕ => 4*(radiusFactor a0)^2*massEnvelope A n) atTop (𝓝 0)
    simpa only [mul_zero] using (massEnvelope_tendsto A).const_mul (4*(radiusFactor a0)^2)
  have hi : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hh := (hs.const_mul (16*(scaleCap a0)^2)).add ((hm.mul hi).const_mul 4)
  change Tendsto (fun n : ℕ => 16*(scaleCap a0)^2*Real.sqrt (A*Real.log (n:ℝ)/(n:ℝ))+
    4*actualMassEnvelope A a0 n/(n:ℝ)) atTop (𝓝 0)
  simpa only [Function.comp_def, Real.sqrt_zero, mul_zero, add_zero,
    div_eq_mul_inv, mul_assoc] using hh

lemma deletionRatio_tendsto (B : ℝ) : Tendsto (deletionRatio B) atTop (𝓝 0) := by
  have hh : Tendsto (fun n : ℕ => Real.log (n:ℝ)/(n:ℝ)) atTop (𝓝 0) := by
    simpa using log_power_decay 1 (by norm_num : (0:ℝ)<1)
  change Tendsto (fun n : ℕ => B*Real.log (n:ℝ)/(n:ℝ)) atTop (𝓝 0)
  simpa only [mul_zero, mul_div_assoc] using hh.const_mul B

lemma kappaRatio_tendsto (A B a0 : ℝ) : Tendsto (kappaRatio A B a0) atTop (𝓝 0) := by
  have hh := (((deletionRatio_tendsto B).mul (deltaEnvelope_tendsto A a0)).const_mul 4).add
    (((deletionRatio_tendsto B).pow 2).const_mul (2*(16*(scaleCap a0)^2+1)))
  change Tendsto (fun n : ℕ => 4*deletionRatio B n*deltaEnvelope A a0 n+
    2*(16*(scaleCap a0)^2+1)*(deletionRatio B n)^2) atTop (𝓝 0)
  simpa only [mul_zero, zero_pow (by norm_num : 2≠0), add_zero, mul_assoc] using hh

lemma totalRatio_tendsto (A B a0 : ℝ) : Tendsto (totalRatio A B a0) atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => deletionRatio B n+kappaRatio A B a0 n) atTop (𝓝 0)
  simpa only [add_zero] using (deletionRatio_tendsto B).add (kappaRatio_tendsto A B a0)

lemma epsilonEnvelope_tendsto (A B a0 : ℝ) : Tendsto (epsilonEnvelope A B a0) atTop (𝓝 0) := by
  have hh := (((deltaEnvelope_tendsto A a0).add ((deletionRatio_tendsto B).const_mul
    (16*(scaleCap a0)^2+1))).add (kappaRatio_tendsto A B a0)).const_mul 2
  change Tendsto (fun n : ℕ => 2*(deltaEnvelope A a0 n+(16*(scaleCap a0)^2+1)*deletionRatio B n+kappaRatio A B a0 n)) atTop (𝓝 0)
  simpa only [mul_zero, add_zero] using hh

lemma actual_delta_le {n : ℕ} (T : Tournament n) {A a0 : ℝ}
    (hτ : tau (normalizedScore T) ≤ A*Real.log (n:ℝ)) :
    normalizedMarginalBound T a0 ≤ deltaEnvelope A a0 n := by
  have ht0 := tau_nonneg (normalizedScore T)
  have hsr : Real.sqrt (tau (normalizedScore T))/Real.sqrt (n:ℝ) ≤
      Real.sqrt (A*Real.log (n:ℝ)/(n:ℝ)) := by
    rw [← Real.sqrt_div ht0]
    exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hτ (Nat.cast_nonneg n))
  unfold normalizedMarginalBound deltaEnvelope
  have hm := actual_mass_le T (a0:=a0) hτ
  calc
    _ = 16*(scaleCap a0)^2*(Real.sqrt (tau (normalizedScore T))/Real.sqrt (n:ℝ))+
      4*massBound T a0/(n:ℝ) := by ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hsr (by positivity))
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hm (by norm_num)) (Nat.cast_nonneg n))

lemma actual_kappaRatio_le {n : ℕ} (hn : 0 < n) (T : Tournament n)
    (I : Finset (Fin n)) {A B a0 : ℝ} (_hA : 0 ≤ A) (hB : 0 ≤ B)
    (hτ : tau (normalizedScore T) ≤ A*Real.log (n:ℝ))
    (ht : (I.card:ℝ) ≤ B*Real.log (n:ℝ)) :
    actualK T a0 I/(n:ℝ) ≤ kappaRatio A B a0 n := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  have hd := actual_delta_le T (a0:=a0) hτ
  have hd0 := normalizedMarginalBound_nonneg T a0
  have hr : (I.card:ℝ)/(n:ℝ) ≤ deletionRatio B n :=
    div_le_div_of_nonneg_right ht (Nat.cast_nonneg n)
  have hrr : 0 ≤ (I.card:ℝ)/(n:ℝ) := by positivity
  have he : actualK T a0 I/(n:ℝ) =
      4*((I.card:ℝ)/(n:ℝ))*normalizedMarginalBound T a0+
        2*(16*(scaleCap a0)^2+1)*((I.card:ℝ)/(n:ℝ))^2 := by
    unfold actualK
    field_simp
  rw [he]
  have hdel0 := deletionRatio_nonneg hB n
  unfold kappaRatio
  gcongr

/-- All three remaining scalar hypotheses hold uniformly over the log window. -/
theorem eventually_remaining_budgets {A B a0 : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∀ᶠ n : ℕ in atTop, ∀ (T : Tournament n) (I : Finset (Fin n)) (m : ℕ),
      (m:ℝ)=(n:ℝ)-(I.card:ℝ) →
      tau (normalizedScore T) ≤ A*Real.log (n:ℝ) →
      (I.card:ℝ) ≤ B*Real.log (n:ℝ) →
      actualK T a0 I < (m:ℝ) ∧ gapBudget n m (39/46) (actualK T a0 I) < 1 ∧
      residualBudget n m I.card (16*(scaleCap a0)^2) (normalizedMarginalBound T a0) (actualK T a0 I) ≤
        RawScalingSynthesis.epsilonThreshold (density m (16*(scaleCap a0)^2) (actualK T a0 I))
          (gapBudget n m (39/46) (actualK T a0 I)) := by
  have heps := RawScalingSynthesis.epsilonThreshold_pos
    (show 0 ≤ 2*(16*(scaleCap a0)^2) by positivity) (by norm_num : (1+(39/46:ℝ))/2<1)
  filter_upwards [eventually_gt_atTop 0,
    (totalRatio_tendsto A B a0).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<(1-39/46)/2)),
    (epsilonEnvelope_tendsto A B a0).eventually (gt_mem_nhds heps)] with n hn hz he
  intro T I m hm hτ ht
  have hd0 := normalizedMarginalBound_nonneg T a0
  have hk0 : 0 ≤ actualK T a0 I := by unfold actualK; positivity
  exact scalar_gate hn hm (by positivity) (by positivity) hd0 hk0 (by norm_num) (by norm_num)
    (deletionRatio_nonneg hB n) (kappaRatio_nonneg hA hB n) (deltaEnvelope_nonneg hA n)
    (div_le_div_of_nonneg_right ht (Nat.cast_nonneg n)) (actual_kappaRatio_le hn T I hA hB hτ ht)
    (actual_delta_le T hτ) hz.le he.le
/-- Eventual actual same-root scaling over the whole fixed logarithmic window.
The final user supplies only score cap, log-energy/deletion windows and the
actual retained-set enumerations, not any smallness or spectral condition. -/
theorem eventually_actual_deleted_scaling {A B a0 : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (h0 : 0 ≤ a0) (h1 : a0<1) :
    ∀ᶠ n : ℕ in atTop, ∀ (T : Tournament n) (m : ℕ)
      (e f : Fin m ↪ Fin n) (I J : Finset (Fin n)),
      Finset.univ.image e=Iᶜ → Finset.univ.image f=Jᶜ → J.card=I.card →
      (m:ℝ)=(n:ℝ)-(I.card:ℝ) →
      (∀ i,|normalizedScore T i| ≤ a0) →
      tau (normalizedScore T) ≤ A*Real.log (n:ℝ) →
      (I.card:ℝ) ≤ B*Real.log (n:ℝ) →
      controlled (actualDeleted T e f I J)
        (density m (16*(scaleCap a0)^2) (actualK T a0 I))
        (residualBudget n m I.card (16*(scaleCap a0)^2)
          (normalizedMarginalBound T a0) (actualK T a0 I))
        (gapBudget n m (39/46) (actualK T a0 I)) := by
  filter_upwards [eventually_ge_atTop 24, eventually_actual_error_small A a0,
    eventually_remaining_budgets (a0:=a0) hA hB,
    (deletionRatio_tendsto B).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))]
    with n hn herr hbud hratio
  intro T m e f I J he hf hcard hm ha hτ ht
  have hbudget := hbud T I m hm hτ ht
  have hk0 : 0 ≤ actualK T a0 I := by
    have hd0 := normalizedMarginalBound_nonneg T a0
    unfold actualK
    positivity
  have hm0 : 0 < m := by exact_mod_cast (lt_of_le_of_lt hk0 hbudget.1)
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0 < n by omega)
  have htRatio : (I.card:ℝ)/(n:ℝ) ≤ 1/2 :=
    (div_le_div_of_nonneg_right ht hnR.le).trans hratio.le
  have htHalf : (2:ℝ)*(I.card:ℝ) ≤ (n:ℝ) := by
    have hh := (div_le_iff₀ hnR).mp htRatio
    linarith
  have hhalf : 2*I.card ≤ n := by exact_mod_cast htHalf
  exact actual_deleted_scaling T hn hm0 e f I J he hf hcard hhalf hm h0 h1 ha
    (herr T hτ) hbudget.1 hbudget.2.1 hbudget.2.2
end LogWindowDeletionBudgetCandidate
