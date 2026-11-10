import CoreMinorThresholdScalarCandidate
set_option autoImplicit false
noncomputable section
namespace CoreMinorEnvelopeCandidate
open Filter
open scoped Topology
open TournamentHamiltonian ActualTournamentPrescalingBounds ActualPrescalingNormalization
open TournamentPrescalingMassBound LogWindowErrorCandidate LogWindowDeletionBudgetCandidate
open DeletedScalingSynthesisCandidate ActualSameRootRateCandidate SameRootPermanentCandidate

def kEnvelope (A B a0 : ℝ) (n : ℕ) : ℝ :=
  4*B*Real.log (n:ℝ)*deltaEnvelope A a0 n+
    2*(16*(scaleCap a0)^2+1)*B^2*Real.log (n:ℝ)^2/(n:ℝ)
def rEnvelope (A B : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (A*Real.log (n:ℝ)/(n:ℝ))+(B*Real.log (n:ℝ)+1)/(n:ℝ)
def error (n : ℕ) : ℝ :=
  deletionRatio 800 n+actualMassEnvelope 1200 (19/20) n+kEnvelope 1200 800 (19/20) n+
  |gaussianConstant (19/20)+64| *rEnvelope 1200 800 n+|fixedError (19/20)|/(n:ℝ)

lemma mass_tendsto (A a0 : ℝ) : Tendsto (actualMassEnvelope A a0) atTop (𝓝 0) := by
  change Tendsto (fun n => 4*(radiusFactor a0)^2*massEnvelope A n) atTop (𝓝 0)
  simpa only [mul_zero] using (massEnvelope_tendsto A).const_mul (4*(radiusFactor a0)^2)

lemma log_delta_tendsto (A a0 : ℝ) :
    Tendsto (fun n : ℕ => Real.log (n:ℝ)*deltaEnvelope A a0 n) atTop (𝓝 0) := by
  have h3 : Tendsto (fun n : ℕ => A*Real.log (n:ℝ)^3/(n:ℝ)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one, mul_div_assoc, mul_zero] using
      (log_power_decay 3 (by norm_num : (0:ℝ)<1)).const_mul A
  have hs : Tendsto (fun n : ℕ => Real.log (n:ℝ)*Real.sqrt (A*Real.log (n:ℝ)/(n:ℝ))) atTop (𝓝 0) := by
    have hh := (Real.continuous_sqrt.tendsto 0).comp h3
    have he (n : ℕ) : Real.sqrt (A*Real.log (n:ℝ)^3/(n:ℝ)) =
        Real.log (n:ℝ)*Real.sqrt (A*Real.log (n:ℝ)/(n:ℝ)) := by
      have heq : A*Real.log (n:ℝ)^3/(n:ℝ)=Real.log (n:ℝ)^2*(A*Real.log (n:ℝ)/(n:ℝ)) := by ring
      rw [heq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (nat_log_nonneg n)]
    simpa only [Function.comp_def, he, Real.sqrt_zero] using hh
  have hl : Tendsto (fun n : ℕ => Real.log (n:ℝ)/(n:ℝ)) atTop (𝓝 0) := by
    simpa using log_power_decay 1 (by norm_num : (0:ℝ)<1)
  have hh := (hs.const_mul (16*(scaleCap a0)^2)).add ((hl.mul (mass_tendsto A a0)).const_mul 4)
  convert hh using 1
  · funext n; unfold deltaEnvelope; ring
  · simp only [mul_zero, add_zero]

lemma kEnvelope_tendsto (A B a0 : ℝ) : Tendsto (kEnvelope A B a0) atTop (𝓝 0) := by
  have h2 : Tendsto (fun n : ℕ => Real.log (n:ℝ)^2/(n:ℝ)) atTop (𝓝 0) := by
    simpa using log_power_decay 2 (by norm_num : (0:ℝ)<1)
  have hh := ((log_delta_tendsto A a0).const_mul (4*B)).add
    (h2.const_mul (2*(16*(scaleCap a0)^2+1)*B^2))
  convert hh using 1
  · funext n; unfold kEnvelope; ring
  · simp only [mul_zero, add_zero]

lemma rEnvelope_tendsto (A B : ℝ) : Tendsto (rEnvelope A B) atTop (𝓝 0) := by
  have hl := deletionRatio_tendsto A
  have hs := (Real.continuous_sqrt.tendsto 0).comp hl
  have hi : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hh := hs.add ((deletionRatio_tendsto B).add hi)
  change Tendsto (fun n : ℕ => Real.sqrt (A*Real.log (n:ℝ)/(n:ℝ))+(B*Real.log (n:ℝ)+1)/(n:ℝ)) atTop (𝓝 0)
  simpa only [deletionRatio, add_div, one_div, Function.comp_def, Real.sqrt_zero, add_zero] using hh

lemma error_tendsto : Tendsto error atTop (𝓝 0) := by
  have hi : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hh := ((((deletionRatio_tendsto 800).add (mass_tendsto 1200 (19/20))).add
    (kEnvelope_tendsto 1200 800 (19/20))).add
    ((rEnvelope_tendsto 1200 800).const_mul |gaussianConstant (19/20)+64|)).add
    (hi.const_mul |fixedError (19/20)|)
  change Tendsto (fun n : ℕ => deletionRatio 800 n+actualMassEnvelope 1200 (19/20) n+kEnvelope 1200 800 (19/20) n+
    |gaussianConstant (19/20)+64| * rEnvelope 1200 800 n+|fixedError (19/20)|/(n:ℝ)) atTop (𝓝 0)
  simpa only [div_eq_mul_inv, mul_zero, add_zero] using hh

lemma actual_k_le {n : ℕ} (T : Tournament n) (I : Finset (Fin n))
    {A B a0 : ℝ} (_hA : 0 ≤ A) (hB : 0 ≤ B)
    (hτ : tau (normalizedScore T) ≤ A*Real.log (n:ℝ))
    (ht : (I.card:ℝ) ≤ B*Real.log (n:ℝ)) : actualK T a0 I ≤ kEnvelope A B a0 n := by
  have hd := actual_delta_le T (a0:=a0) hτ
  have hd0 := normalizedMarginalBound_nonneg T a0
  have ht0 : (0:ℝ) ≤ I.card := Nat.cast_nonneg _
  have hB0 : 0 ≤ B*Real.log (n:ℝ) := ht0.trans ht
  unfold actualK kEnvelope
  calc
    _ ≤ 4*(B*Real.log (n:ℝ))*deltaEnvelope A a0 n+
        2*(16*(scaleCap a0)^2+1)*(B*Real.log (n:ℝ))^2/(n:ℝ) := by gcongr
    _ = _ := by ring

lemma actual_r_le {n : ℕ} (T : Tournament n) (I : Finset (Fin n)) {A B : ℝ}
    (hτ : tau (normalizedScore T) ≤ A*Real.log (n:ℝ))
    (ht : (I.card:ℝ) ≤ B*Real.log (n:ℝ)) :
    ActualNormalizationRateCandidate.rate T I.card ≤ rEnvelope A B n := by
  unfold ActualNormalizationRateCandidate.rate rEnvelope
  gcongr
end CoreMinorEnvelopeCandidate
