import CoreMinorEnvelopeCandidate
set_option autoImplicit false
noncomputable section
namespace CoreMinorThresholdCandidate
open Filter Finset
open scoped Topology
open TournamentHamiltonian ActualTournamentPrescalingBounds ActualPrescalingNormalization
open TournamentPrescalingMassBound DeletedScalingSynthesisCandidate ActualKappaBridgeCandidate
open ActualSameRootRateCandidate ActualNormalizationRateCandidate SameRootPermanentCandidate
open RealProjectionAggregationCandidate SkewBaselineGramDifferenceCandidate
open GeneralScalarRestorationCandidate CoreMinorThresholdScalarCandidate CoreMinorEnvelopeCandidate
open LogWindowErrorCandidate LogWindowDeletionBudgetCandidate

theorem eventually_core_minor :
    ∀ᶠ n : ℕ in atTop, ∀ (T : Tournament n) (m : ℕ) (I J : Finset (Fin n))
      (r : Fin m ≃ {i // i∈Iᶜ}) (c : Fin m ≃ {j // j∈Jᶜ}),
      (∀ i, |normalizedScore T i|≤19/20) →
      tau (normalizedScore T)≤1200*Real.log (n:ℝ) → (I.card:ℝ)≤800*Real.log (n:ℝ) →
      ((ActualReconstructionBridgeCandidate.adjacency T).submatrix
        (complementEmbedding I r) (complementEmbedding J c)).permanent ≤
      2*Real.exp (-1+error n)*((m.factorial:ℝ)/(2:ℝ)^m)*
        (∏ i∈I,(1+normalizedScore T i)⁻¹)*(∏ j∈J,(1-normalizedScore T j)⁻¹) := by
  filter_upwards [eventually_ge_atTop 2,
    ActualCappedMinorUpperCandidate.eventually_actual_capped_minor_upper
      (by norm_num : (0:ℝ)≤1200) (by norm_num : (0:ℝ)≤800)
      (by norm_num : (0:ℝ)≤19/20) (by norm_num : (19/20:ℝ)<1)] with n hn hu
  intro T m I J r c ha hτ ht
  have hn0 : 0 < n := by omega
  have hnR : (0:ℝ)<n := by exact_mod_cast hn0
  have hm := actual_mass_le T (a0:=19/20) hτ
  have hk := actual_k_le T I (a0:=19/20) (by norm_num : (0:ℝ)≤1200) (by norm_num : (0:ℝ)≤800) hτ ht
  have hr := actual_r_le T I hτ ht
  have hrate := (rate_components T I.card hn0).1
  let e := |gaussianConstant (19/20)+64| * rEnvelope 1200 800 n
  let d := |fixedError (19/20)|/(n:ℝ)
  have he : 0 ≤ e := mul_nonneg (abs_nonneg _) (hrate.trans hr)
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hgauss : (gaussianConstant (19/20)+64)*rate T I.card ≤ e := by
    exact (mul_le_mul_of_nonneg_right (le_abs_self _) hrate).trans
      (mul_le_mul_of_nonneg_left hr (abs_nonneg _))
  have hb : Real.exp (g (scaled (signMatrix T))+(gaussianConstant (19/20)+64)*rate T I.card)+
      2*|fixedError (19/20)|/(n:ℝ) ≤ 2*Real.exp (e+d) := by
    have hh := absorb_additive (gaussian_upper T hn0) he hd
    calc
      _ ≤ Real.exp (g (scaled (signMatrix T))+e)+2*d := by
        dsimp [d]
        rw [mul_div_assoc]
        exact add_le_add (Real.exp_le_exp.mpr (add_le_add le_rfl hgauss)) le_rfl
      _ ≤ _ := hh
  let W := (∏ i∈I,(1+normalizedScore T i)⁻¹)*(∏ j∈J,(1-normalizedScore T j)⁻¹)
  have hO := omittedGamma_nonneg T I J (fun i => (ha i).trans_lt (by norm_num))
  have hOW : omittedGamma T I J ≤ W := omittedGamma_upper T I J (by norm_num) (by norm_num) ha
  have hW : 0 ≤ W := hO.trans hOW
  have ht' : (I.card:ℝ)/(n:ℝ) ≤ deletionRatio 800 n :=
    div_le_div_of_nonneg_right ht hnR.le
  have hex : -1+(I.card:ℝ)/(n:ℝ)+massBound T (19/20)+actualK T (19/20) I+(e+d) ≤ -1+error n := by
    dsimp [error,e,d]
    linarith
  have hbase : 0 ≤ (m.factorial:ℝ)/(2:ℝ)^m := by positivity
  calc
    _ ≤ omittedGamma T I J*((m.factorial:ℝ)/(2:ℝ)^m)*
        Real.exp (-1+(I.card:ℝ)/(n:ℝ)+massBound T (19/20)+actualK T (19/20) I)*
        (2*Real.exp (e+d)) := (hu T m I J r c ha hτ ht).trans
          (mul_le_mul_of_nonneg_left hb (by positivity))
    _ ≤ W*((m.factorial:ℝ)/(2:ℝ)^m)*
        Real.exp (-1+(I.card:ℝ)/(n:ℝ)+massBound T (19/20)+actualK T (19/20) I)*
        (2*Real.exp (e+d)) := by gcongr
    _ = 2*W*((m.factorial:ℝ)/(2:ℝ)^m)*
        Real.exp (-1+(I.card:ℝ)/(n:ℝ)+massBound T (19/20)+actualK T (19/20) I+(e+d)) := by simp only [Real.exp_add]; ring
    _ ≤ 2*W*((m.factorial:ℝ)/(2:ℝ)^m)*Real.exp (-1+error n) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hex) (by positivity)
    _ = _ := by dsimp [W]; ring
end CoreMinorThresholdCandidate
