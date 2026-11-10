import UnitMinorErrorBudgetCandidate
import ActualReferenceGaussianBridge
/-! Verified actual signed lower endpoint. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace ActualUnitMinorLowerCandidate
open Matrix Finset Filter
open scoped Topology
open TournamentHamiltonian ActualTournamentPrescalingBounds ActualPrescalingNormalization
open TournamentPrescalingMassBound ActualKappaBridgeCandidate ActualControlledReconstructionCandidate
open MatrixScalingMassPotential PhysicalMinorRecoveryCandidate ActualRecoveryUpperCandidate
open ActualSameRootRateCandidate ActualNormalizationRateCandidate SameRootPermanentCandidate
open UnitScorePrefactorCandidate UnitScoreEnvelopesCandidate UnitScorePotentialBudgetCandidate
open ActualUnitScorePrefactorCandidate MinorNormalizationCandidate SignedMinorScalarCandidate
open UnitMinorErrorBudgetCandidate ActualReferenceGaussianBridge
open RealProjectionAggregationCandidate SkewBaselineGramDifferenceCandidate

theorem eventually_actual_signed_minor_lower :
    ∀ᶠ n : ℕ in atTop, ∀ (T : Tournament n) (m : ℕ) (U : Finset (Fin n))
      (_r : Fin m ≃ {i // i∈Uᶜ}),
      (∀ i, |score T i|≤1) → (U.card:ℝ)≤Real.log (n:ℝ) →
      Real.exp (-1)*gaussianFactor T*((m.factorial:ℝ)/(2:ℝ)^m)*
        (1-UnitMinorErrorBudgetCandidate.lowerConstant*((U.card:ℝ)+2)^2/(n:ℝ)) ≤
      ((TournamentHamiltonian.adjacency T).submatrix
        (Subtype.val : (Uᶜ : Finset (Fin n))→Fin n) Subtype.val).permanent := by
  have hlog : ∀ᶠ n : ℕ in atTop, (1:ℝ)≤Real.log (n:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  filter_upwards [eventually_ge_atTop 16, hlog, eventual_short_small,
    eventually_unit_prefactor (B:=1) (by norm_num),
    ActualPrincipalPathRecoveryCandidate.eventually_actual_principal_sandwich
      (A:=4) (B:=1) (a0:=1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    (LogWindowDeletionBudgetCandidate.deletionRatio_tendsto 1).eventually
      (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))] with n hn hlog hsmall hF hp hratio
  intro T m U r hs ht
  have hn0 : 0<n := by omega
  have hnR : (0:ℝ)<n := by exact_mod_cast hn0
  have hn4 : 4≤n := by omega
  have hcaps := unit_score_caps T hn4 hs
  have hτ : tau (normalizedScore T)≤4*Real.log (n:ℝ) := by linarith [hcaps.2.2.2]
  have ht1 : (U.card:ℝ)≤1*Real.log (n:ℝ) := by simpa using ht
  obtain ⟨x,y,hw,hl,hu⟩ := hp T m U r hcaps.2.1 hτ ht1
  have hff := hF T m U r hs ht1 x y hw.1
  have hdim := complement_card U r
  have hmle : m≤n := by
    have hh : (m:ℝ)≤n := by linarith [show (0:ℝ)≤U.card from Nat.cast_nonneg _]
    exact_mod_cast hh
  have hkn : (U.card:ℝ)/(n:ℝ)≤1/2 :=
    (div_le_div_of_nonneg_right ht hnR.le).trans (by simpa [LogWindowDeletionBudgetCandidate.deletionRatio] using hratio.le)
  have hhalf : (n:ℝ)/2≤ m := by have hh := (div_le_iff₀ hnR).mp hkn; linarith
  have hmR : (0:ℝ)< m := by linarith
  have hm : 0 < m := by exact_mod_cast hmR
  let b : ℝ := (m.factorial:ℝ)/(2:ℝ)^m
  let A : ℝ := (1-1/(n:ℝ))^m*fullPrefactor T U x y
  let E : ℝ := (gaussianConstant (1/2)+64)*rate T U.card
  let d : ℝ := 2/(n:ℝ)+fullConstant*((U.card:ℝ)+1)^2/(n:ℝ)
  let h : ℝ := |fixedError (1/2)|/(m:ℝ)
  have hb : 0<b := by dsimp [b]; positivity
  have hq := deletion_scalar_bounds (show 2≤n by omega) hmle
  have hA0 : 0≤A := by dsimp [A]; exact mul_nonneg ((Real.exp_pos _).le.trans hq.1) hff.2.1.le
  have heSmall : fullConstant*((U.card:ℝ)+1)^2/(n:ℝ)≤1 := by
    apply le_trans ?_ hsmall
    apply div_le_div_of_nonneg_right ?_ hnR.le
    apply mul_le_mul_of_nonneg_left ?_ constants_nonneg.1
    nlinarith [show (0:ℝ)≤U.card from Nat.cast_nonneg _]
  have hAu : A≤Real.exp 1 := by
    have hfexp := hff.2.2.2.2.trans (Real.exp_le_exp.mpr heSmall)
    dsimp [A]
    exact (mul_le_mul hq.2 hfexp hff.2.1.le (by norm_num)).trans_eq (one_mul _)
  have hAl : Real.exp (-1-d)≤A := by
    have hh := mul_le_mul hq.1 hff.2.2.2.1 (Real.exp_pos _).le ((Real.exp_pos _).le.trans hq.1)
    dsimp [A,d] at *
    rw [← Real.exp_add] at hh
    convert hh using 1 ; congr 1 ; ring
  have hG := one_le_gaussianFactor T hn0
  have hfactor : recoveryFactor T U U m*Real.exp (-shiftedPotential T U U x y)*base m=b*A := by
    rw [exact_full_prefactor T U x y hn0 (fun i => (hcaps.2.1 i).trans_lt (by norm_num))]
    have hh := referenceScale_base n m hn0 hm
    dsimp [b,A]
    calc
      _ = (referenceScale n m*base m)*fullPrefactor T U x y := by ring
      _ = _ := by rw [hh]; ring
  have hP : A*(gaussianFactor T*Real.exp (-E)-h)≤
      ((TournamentHamiltonian.adjacency T).submatrix
        (Subtype.val : (Uᶜ : Finset (Fin n))→Fin n) Subtype.val).permanent/b := by
    rw [hfactor, Real.exp_sub, ← gaussianFactor_eq_exp_g T hn0] at hl
    have he : gaussianFactor T/Real.exp E=gaussianFactor T*Real.exp (-E) := by rw [Real.exp_neg]; rfl
    change b*A*(gaussianFactor T/Real.exp E-fixedError (1/2)/(m:ℝ))≤_ at hl
    rw [he] at hl
    apply (le_div_iff₀ hb).mpr
    have herr : fixedError (1/2)/(m:ℝ)≤h := div_le_div_of_nonneg_right (le_abs_self _) hmR.le
    have hh := mul_le_mul_of_nonneg_left herr (mul_nonneg hb.le hA0)
    nlinarith only [hl,hh]
  have hlow := signed_lower hG (show 0≤h by dsimp [h]; positivity) hA0 hAl hAu hP
  have hE := rate_budget T hn4 hs U.card
  have he : h≤2*|fixedError (1/2)|/(n:ℝ) := by
    dsimp [h]
    calc
      _ ≤ |fixedError (1/2)|/((n:ℝ)/2) := div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hhalf
      _ = _ := by ring
  have hbudget : d+E+Real.exp 2*h≤UnitMinorErrorBudgetCandidate.lowerConstant*((U.card:ℝ)+2)^2/(n:ℝ) := by
    have hi : (0:ℝ)≤(n:ℝ)⁻¹ := inv_nonneg.mpr hnR.le
    have ht0 : (0:ℝ)≤U.card := Nat.cast_nonneg _
    have hsq : ((U.card:ℝ)+1)^2≤((U.card:ℝ)+2)^2 := by nlinarith
    have hsq1 : (1:ℝ)≤((U.card:ℝ)+2)^2 := by nlinarith
    have hfc := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsq hi) constants_nonneg.1
    have hgc := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsq hi) (show 0≤3*(gaussianConstant (1/2)+64) by linarith [constants_nonneg.2.1])
    have hunit := mul_le_mul_of_nonneg_right hsq1 hi
    have herr := mul_le_mul_of_nonneg_left he (Real.exp_pos 2).le
    have herr2 := mul_le_mul_of_nonneg_left hunit (show 0≤2*Real.exp 2*|fixedError (1/2)| by positivity)
    dsimp [d,E] at *
    unfold UnitMinorErrorBudgetCandidate.lowerConstant
    simp only [div_eq_mul_inv] at hE herr ⊢
    nlinarith only [hfc,hgc,hunit,herr,herr2,hE]
  have hscaled := mul_le_mul_of_nonneg_left hbudget
    (mul_nonneg (Real.exp_pos (-1)).le (by linarith : 0≤gaussianFactor T))
  have htarg : Real.exp (-1)*gaussianFactor T*(1-UnitMinorErrorBudgetCandidate.lowerConstant*((U.card:ℝ)+2)^2/(n:ℝ))≤
      ((TournamentHamiltonian.adjacency T).submatrix
        (Subtype.val : (Uᶜ : Finset (Fin n))→Fin n) Subtype.val).permanent/b := by
    nlinarith only [hlow,hscaled]
  have hh := (le_div_iff₀ hb).mp htarg
  dsimp [b] at hh
  nlinarith only [hh]
end ActualUnitMinorLowerCandidate
