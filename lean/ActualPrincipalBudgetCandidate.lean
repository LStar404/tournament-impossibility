import ActualCappedMinorUpperCandidate
import ActualReferenceGaussianBridge
set_option autoImplicit false
noncomputable section
namespace ActualPrincipalBudgetCandidate
open TournamentHamiltonian ActualTournamentPrescalingBounds ActualPrescalingNormalization
open TournamentPrescalingMassBound DeletedScalingSynthesisCandidate ActualNormalizationRateCandidate
open ActualSameRootRateCandidate SameRootPermanentCandidate GeneralScalarRestorationCandidate
open LogWindowDeletionBudgetCandidate LogWindowErrorCandidate Filter
open scoped Topology

def budget (n : ℕ) (t τ : ℝ) : ℝ :=
  Real.sqrt (τ/n)+(t+1)/n+((τ+τ^2)/n+τ*Real.sqrt (τ/n))+
    t*Real.sqrt (τ/n)+t^2/n
lemma budget_nonneg (n : ℕ) {t τ : ℝ} (ht : 0 ≤ t) (hτ : 0 ≤ τ) : 0 ≤ budget n t τ := by
  unfold budget
  positivity
lemma budget_card_split (n : ℕ) (t τ : ℝ) :
    budget n t τ=budget n 0 τ+t*(Real.sqrt (τ/n)+1/n)+t^2/n := by
  unfold budget
  ring

def constant (a0 : ℝ) : ℝ :=
  1+4*(radiusFactor a0)^2+4*deltaConstant a0+2*(16*(scaleCap a0)^2+1)+
    |gaussianConstant a0+64|+2*|fixedError a0|
lemma constant_nonneg (a0 : ℝ) : 0 ≤ constant a0 := by
  unfold constant deltaConstant
  positivity
lemma mass_identity {n : ℕ} (T : Tournament n) (a0 : ℝ) :
    massBound T a0=4*(radiusFactor a0)^2*
      ((tau (normalizedScore T)+(tau (normalizedScore T))^2)/n+
        tau (normalizedScore T)*Real.sqrt (tau (normalizedScore T)/n)) := by
  unfold massBound errorScale
  rw [Real.sqrt_div (tau_nonneg _)]
  ring
lemma eventually_mass_le_one {A a0 : ℝ} :
    ∀ᶠ n : ℕ in atTop, ∀ T : Tournament n,
      tau (normalizedScore T) ≤ A*Real.log (n:ℝ) → massBound T a0 ≤ 1 := by
  have hmass : Tendsto (actualMassEnvelope A a0) atTop (𝓝 0) := by
    change Tendsto (fun n => 4*(radiusFactor a0)^2*massEnvelope A n) atTop (𝓝 0)
    simpa only [mul_zero] using (massEnvelope_tendsto A).const_mul (4*(radiusFactor a0)^2)
  filter_upwards [hmass.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))] with n hn T htau
  exact (actual_mass_le T htau).trans hn.le
lemma finite_exponent_budget {n : ℕ} (T : Tournament n) (I : Finset (Fin n))
    (hn : 0 < n) (a0 : ℝ) (hM : massBound T a0 ≤ 1) :
    (I.card:ℝ)/n+massBound T a0+actualK T a0 I+
      |gaussianConstant a0+64| *rate T I.card+2*|fixedError a0|/n  ≤ 
      constant a0*budget n I.card (tau (normalizedScore T)) := by
  let τ := tau (normalizedScore T)
  let t : ℝ := I.card
  let s := Real.sqrt (τ/n)
  let e := (τ+τ^2)/n+τ*s
  let b := budget n t τ
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have ht : 0 ≤ t := Nat.cast_nonneg _
  have hτ : 0 ≤ τ := tau_nonneg _
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have he : 0 ≤ e := by dsimp [e]; positivity
  have htn : 0 ≤ t/(n:ℝ) := by positivity
  have hi : 0 ≤ (1:ℝ)/(n:ℝ) := by positivity
  have hts : 0 ≤ t*s := mul_nonneg ht hs
  have ht2 : 0 ≤ t^2/(n:ℝ) := by positivity
  have hb : b=s+t/n+1/n+e+t*s+t^2/n := by dsimp [b,budget,s,e]; ring
  have htb : t/(n:ℝ) ≤ b := by linarith
  have heb : e ≤ b := by linarith
  have hib : (1:ℝ)/(n:ℝ) ≤ b := by linarith
  have hsb : t*(s+1/n) ≤ b := by rw [mul_add,mul_one_div]; linarith
  have ht2b : t^2/(n:ℝ) ≤ b := by linarith
  have hr : rate T I.card ≤ b := by unfold rate; change s+(t+1)/n ≤ b; rw [add_div]; linarith
  have hmass : massBound T a0 ≤ 4*(radiusFactor a0)^2*b := by
    rw [mass_identity]
    exact mul_le_mul_of_nonneg_left heb (by positivity)
  have hdelta := actual_delta_rate T 0 hn a0 hM
  have hr0 : rate T 0=s+1/n := by simp [rate,s,τ]
  rw [hr0] at hdelta
  have hd0 : 0 ≤ deltaConstant a0 := by unfold deltaConstant; positivity
  have hk : actualK T a0 I ≤ 
      (4*deltaConstant a0+2*(16*(scaleCap a0)^2+1))*b := by
    have h1 := mul_le_mul_of_nonneg_left hdelta (show 0 ≤ 4*t by positivity)
    have h2 := mul_le_mul_of_nonneg_left hsb (show 0 ≤ 4*deltaConstant a0 by positivity)
    have h3 := mul_le_mul_of_nonneg_left ht2b
      (show 0 ≤ 2*(16*(scaleCap a0)^2+1) by positivity)
    unfold actualK
    change 4*t*normalizedMarginalBound T a0+2*(16*(scaleCap a0)^2+1)*t^2/n ≤ _
    ring_nf at h1 h2 h3 ⊢
    linarith
  have hg := mul_le_mul_of_nonneg_left hr (abs_nonneg (gaussianConstant a0+64))
  have hf := mul_le_mul_of_nonneg_left hib (show 0 ≤ 2*|fixedError a0| by positivity)
  unfold constant
  change t/n+massBound T a0+actualK T a0 I+|gaussianConstant a0+64| *rate T I.card+
    2*|fixedError a0|/n ≤ _
  change _ ≤ (1+4*(radiusFactor a0)^2+4*deltaConstant a0+2*(16*(scaleCap a0)^2+1)+
    |gaussianConstant a0+64|+2*|fixedError a0|)*b
  ring_nf at htb hmass hk hg hf ⊢
  linarith

lemma absorb_p0 {G h d : ℝ} (hG : 1 ≤ G) (hh : 0 ≤ h) (hd : 0 ≤ d) :
    G*Real.exp h+d ≤ G*Real.exp (h+d) := by
  have he := Real.add_one_le_exp d
  have hexp : 1 ≤ Real.exp h := Real.one_le_exp_iff.mpr hh
  rw [Real.exp_add]
  nlinarith [mul_le_mul_of_nonneg_left he (show 0 ≤ G*Real.exp h by positivity),
    mul_le_mul_of_nonneg_right hG (Real.exp_nonneg h)]
theorem eventually_actual_principal_upper {A B a0 : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (h0 : 0 ≤ a0) (h1 : a0 < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ (T : Tournament n) (m : ℕ) (U : Finset (Fin n))
      (r : Fin m ≃ {i // i∈Uᶜ}),
      (∀ i, |normalizedScore T i| ≤ a0) →
      tau (normalizedScore T) ≤ A*Real.log (n:ℝ) → (U.card:ℝ) ≤ B*Real.log (n:ℝ) →
      ((ActualReconstructionBridgeCandidate.adjacency T).submatrix
        (ActualKappaBridgeCandidate.complementEmbedding U r)
        (ActualKappaBridgeCandidate.complementEmbedding U r)).permanent  ≤ 
      omittedGamma T U U*((m.factorial:ℝ)/(2:ℝ)^m)*gaussianFactor T*
        Real.exp (-1+constant a0*budget n U.card (tau (normalizedScore T))) := by
  filter_upwards [ActualCappedMinorUpperCandidate.eventually_actual_capped_minor_upper hA hB h0 h1,
    eventually_mass_le_one (A:=A) (a0:=a0), eventually_ge_atTop (1:ℕ)]
    with n hup hmass hn T m U r ha hτ ht
  have hn0 : 0 < n := by omega
  have hnR : (0:ℝ) < n := by exact_mod_cast hn0
  have hupper := hup T m U U r r ha hτ ht
  have hG := ActualReferenceGaussianBridge.one_le_gaussianFactor T hn0
  have hr := (rate_components T U.card hn0).1
  have hcoeff : (gaussianConstant a0+64)*rate T U.card  ≤ 
      |gaussianConstant a0+64| *rate T U.card := mul_le_mul_of_nonneg_right (le_abs_self _) hr
  have hmain : Real.exp (RealProjectionAggregationCandidate.g
      (SkewBaselineGramDifferenceCandidate.scaled (signMatrix T))+
      (gaussianConstant a0+64)*rate T U.card)+2*|fixedError a0|/n  ≤ 
      gaussianFactor T*Real.exp (|gaussianConstant a0+64| *rate T U.card+2*|fixedError a0|/n) := by
    have he := Real.exp_le_exp.mpr (add_le_add_left hcoeff
      (RealProjectionAggregationCandidate.g (SkewBaselineGramDifferenceCandidate.scaled (signMatrix T))))
    have ha := absorb_p0 (h:=|gaussianConstant a0+64| * rate T U.card)
      (d:=2*|fixedError a0|/n) hG (mul_nonneg (abs_nonneg _) hr) (by positivity)
    calc
      _ ≤ Real.exp (RealProjectionAggregationCandidate.g
          (SkewBaselineGramDifferenceCandidate.scaled (signMatrix T))+
          |gaussianConstant a0+64| * rate T U.card)+2*|fixedError a0|/n := by simpa only [add_comm] using add_le_add_right he (2*|fixedError a0|/n)
      _ ≤ _ := by
        rw [Real.exp_add, ←ActualReferenceGaussianBridge.gaussianFactor_eq_exp_g T hn0]
        exact ha
  have hf0 : 0 ≤ omittedGamma T U U*((m.factorial:ℝ)/(2:ℝ)^m) :=
    mul_nonneg (omittedGamma_nonneg T U U (fun i => (ha i).trans_lt h1)) (by positivity)
  have he := finite_exponent_budget T U hn0 a0 (hmass T hτ)
  have hmul := mul_le_mul_of_nonneg_left hmain
    (mul_nonneg hf0 (Real.exp_nonneg (-1+(U.card:ℝ)/n+massBound T a0+actualK T a0 U)))
  have hcombined :
    (omittedGamma T U U*((m.factorial:ℝ)/(2:ℝ)^m)*
      Real.exp (-1+(U.card:ℝ)/n+massBound T a0+actualK T a0 U))*
      (gaussianFactor T*Real.exp (|gaussianConstant a0+64| *rate T U.card+2*|fixedError a0|/n)) =
    (omittedGamma T U U*((m.factorial:ℝ)/(2:ℝ)^m)*gaussianFactor T)*
      Real.exp (-1+((U.card:ℝ)/n+massBound T a0+actualK T a0 U+
        |gaussianConstant a0+64| *rate T U.card+2*|fixedError a0|/n)) := by
    simp only [Real.exp_add]
    ring
  rw [hcombined] at hmul
  exact (hupper.trans hmul).trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (by linarith)) (mul_nonneg hf0 (by linarith)))
end ActualPrincipalBudgetCandidate
