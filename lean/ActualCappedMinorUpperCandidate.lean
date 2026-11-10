import GeneralScalarRestorationCandidate
import ActualPermanentExponentialCandidate
import SameRootPermanentCandidate
/-! Actual independent-minor upper endpoint. -/
set_option autoImplicit false
noncomputable section
namespace ActualCappedMinorUpperCandidate
open Matrix Finset Filter
open scoped Topology
open TournamentHamiltonian ActualTournamentPrescalingBounds ActualPrescalingNormalization
open TournamentPrescalingMassBound DeletedScalingSynthesisCandidate LogWindowDeletionBudgetCandidate
open ActualReconstructionBridgeCandidate ActualKappaBridgeCandidate ActualControlledReconstructionCandidate
open MatrixScalingMassPotential PhysicalMinorRecoveryCandidate ActualRecoveryUpperCandidate
open ActualSameRootRateCandidate ActualNormalizationRateCandidate SameRootPermanentCandidate
open RealProjectionAggregationCandidate SkewBaselineGramDifferenceCandidate
open GeneralScalarRestorationCandidate

theorem eventually_actual_capped_minor_upper {A B a0 : ℝ}
    (hA : 0≤A) (hB : 0≤B) (h0 : 0≤a0) (h1 : a0<1) :
    ∀ᶠ n : ℕ in atTop, ∀ (T : Tournament n) (m : ℕ) (I J : Finset (Fin n))
      (r : Fin m ≃ {i // i∈Iᶜ}) (c : Fin m ≃ {j // j∈Jᶜ}),
      (∀ i, |normalizedScore T i|≤a0) →
      tau (normalizedScore T)≤A*Real.log (n:ℝ) → (I.card:ℝ)≤B*Real.log (n:ℝ) →
      ((ActualReconstructionBridgeCandidate.adjacency T).submatrix
        (complementEmbedding I r) (complementEmbedding J c)).permanent ≤
      omittedGamma T I J*((m.factorial:ℝ)/(2:ℝ)^m)*
        Real.exp (-1+(I.card:ℝ)/(n:ℝ)+massBound T a0+actualK T a0 I)*
        (Real.exp (g (scaled (signMatrix T))+(gaussianConstant a0+64)*rate T I.card)+
          2*|fixedError a0|/(n:ℝ)) := by
  filter_upwards [eventually_ge_atTop 2, eventually_actual_reconstruction hA hB h0 h1,
    ActualPermanentExponentialCandidate.eventually_actual_permanent_sandwich hA hB h0 h1,
    (deletionRatio_tendsto B).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))]
    with n hn hr hp htmax
  intro T m I J r c ha hτ ht
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hdim := complement_card I r
  have hcard := complement_card_eq I J r c
  have hratio : (I.card:ℝ)/(n:ℝ)≤1/2 :=
    (div_le_div_of_nonneg_right ht hnR.le).trans htmax.le
  have hhalfR : (2:ℝ)*(I.card:ℝ)≤n := by have hh := (div_le_iff₀ hnR).mp hratio; linarith
  have hhalf : 2*I.card≤n := by exact_mod_cast hhalfR
  have hmhalf : (n:ℝ)/2≤(m:ℝ) := by linarith
  have hmR : (0:ℝ)< m := by linarith
  have hm : 0 < m := by exact_mod_cast hmR
  obtain ⟨x,y,hw⟩ := hr T m I J r c ha hτ ht
  have hnorm := (hp T m I J r c hcard ha hτ ht x y hw.1).2
  have hraw := same_root_permanent_upper T I J r c hn h0 h1 ha _ _ _ x y hw
  have hk := actual_independent_deletion_bound T hn h0 h1 ha I J hcard hhalf
  change |IndependentDeletionMass.deletionExcess (normalizedMatrix T) I J|≤actualK T a0 I at hk
  have hκ := (le_abs_self _).trans hk
  let H := Real.exp (g (scaled (signMatrix T))+(gaussianConstant a0+64)*rate T I.card)+
    2*|fixedError a0|/(n:ℝ)
  have hH : 0≤H := by dsimp [H]; positivity
  have herr : fixedError a0/(m:ℝ)≤2*|fixedError a0|/(n:ℝ) := by
    calc
      _ ≤ |fixedError a0|/(m:ℝ) := div_le_div_of_nonneg_right (le_abs_self _) hmR.le
      _ ≤ |fixedError a0|/((n:ℝ)/2) := div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hmhalf
      _ = _ := by ring
  have hM : (expScaled (actualDeleted T (complementEmbedding I r) (complementEmbedding J c) I J) x y).permanent≤base m*H := by
    have hh : (expScaled (actualDeleted T (complementEmbedding I r) (complementEmbedding J c) I J) x y).permanent/base m≤H := by
      exact hnorm.trans (add_le_add le_rfl herr)
    have hh' := (div_le_iff₀ (base_pos hm)).mp hh
    simpa only [mul_comm] using hh'
  have hR := recoveryFactor_nonnegative T I J m hn h0 h1 ha
  have hscale := recovery_scale_upper T I J hn hm hdim h0 h1 ha
  have hW : 0≤omittedGamma T I J*((m.factorial:ℝ)/(2:ℝ)^m) :=
    mul_nonneg (omittedGamma_nonneg T I J (fun i => (ha i).trans_lt h1)) (by positivity)
  have hfac : recoveryFactor T I J m*base m*
      Real.exp (IndependentDeletionMass.deletionExcess (normalizedMatrix T) I J) ≤
      omittedGamma T I J*((m.factorial:ℝ)/(2:ℝ)^m)*
        Real.exp (-1+(I.card:ℝ)/(n:ℝ)+massBound T a0+actualK T a0 I) := by
    have hh := mul_le_mul hscale (Real.exp_le_exp.mpr hκ) (Real.exp_pos _).le
      (mul_nonneg hW (Real.exp_pos _).le)
    simpa only [Real.exp_add, mul_assoc] using hh
  calc
    _ ≤ recoveryFactor T I J m*Real.exp (IndependentDeletionMass.deletionExcess (normalizedMatrix T) I J)*
        (base m*H) := hraw.trans (mul_le_mul_of_nonneg_left hM (mul_nonneg hR (Real.exp_pos _).le))
    _ = (recoveryFactor T I J m*base m*Real.exp (IndependentDeletionMass.deletionExcess (normalizedMatrix T) I J))*H := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hfac hH
end ActualCappedMinorUpperCandidate
