import ActualNormalizationRateCandidate
import SameRootUniformCapsCandidate
import ActualDeletedCenteredGaussianCandidate
import GaussianDisplacement
/-! Isolated finite rate proof. Same supplied root throughout. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace ActualSameRootRateCandidate
open Matrix Finset Filter
open scoped Topology Matrix.Norms.L2Operator
open TournamentHamiltonian ActualTournamentPrescalingBounds ActualPrescalingNormalization
open TournamentPrescalingMassBound DeletedScalingSynthesisCandidate LogWindowDeletionBudgetCandidate
open SameRootFrobeniusCandidate LogWindowFrobeniusUniformCandidate
open IndependentCenteringEnergyCandidate ActualReconstructionBridgeCandidate
open ActualHessianFinite MatrixScalingMassPotential RealBilinearTrace RealGramEndpoint
open FiniteCenteredDisplacementCandidate ActualNormalizationRateCandidate
open ActualTournamentDisplacementCandidate LogWindowErrorCandidate

theorem eventually_displacement_rate {A B a0 : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (h0 : 0 ≤ a0) (h1 : a0 < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ (T : Tournament n) (m : ℕ)
      (e f : Fin m ↪ Fin n) (I J : Finset (Fin n)),
      univ.image e=Iᶜ → univ.image f=Jᶜ → J.card=I.card →
      (m:ℝ)=(n:ℝ)-(I.card:ℝ) →
      (∀ i, |normalizedScore T i| ≤ a0) →
      tau (normalizedScore T) ≤ A*Real.log (n:ℝ) →
      (I.card:ℝ) ≤ B*Real.log (n:ℝ) →
      ∀ x y : Fin m → ℝ,
      controlledWitness (actualDeleted T e f I J)
        (density m (16*(scaleCap a0)^2) (actualK T a0 I))
        (residualBudget n m I.card (16*(scaleCap a0)^2) (normalizedMarginalBound T a0) (actualK T a0 I))
        (gapBudget n m (39/46) (actualK T a0 I)) x y →
      fnorm (expScaled (actualDeleted T e f I J) x y-P m-center ((realZ T).submatrix e f)) ≤ displacementConstant a0*rate T I.card := by
  have hmass : Tendsto (actualMassEnvelope A a0) atTop (𝓝 0) := by
    change Tendsto (fun n => 4*(radiusFactor a0)^2*massEnvelope A n) atTop (𝓝 0)
    simpa only [mul_zero] using (massEnvelope_tendsto A).const_mul (4*(radiusFactor a0)^2)
  filter_upwards [eventually_ge_atTop 24,
    eventually_actual_same_root_displacement hA hB h0 h1,
    hmass.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1)),
    (totalRatio_tendsto A B a0).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/4))]
    with n hn hdisp hmass hratio
  intro T m e f I J he hf hcard hdim ha htau ht x y hw
  have hn0 : 0<n := by omega
  have hnR : (0:ℝ)<n := by exact_mod_cast hn0
  have hM : massBound T a0 ≤ 1 := (actual_mass_le T htau).trans hmass.le
  have hk0 : 0≤actualK T a0 I := by
    have hδ := normalizedMarginalBound_nonneg T a0
    unfold actualK
    positivity
  have hr : ((I.card:ℝ)+actualK T a0 I)/(n:ℝ) ≤ 1/4 := by
    rw [add_div]
    exact (add_le_add (div_le_div_of_nonneg_right ht hnR.le)
      (actual_kappaRatio_le hn0 T I hA hB htau ht)).trans hratio.le
  have hs := (div_le_iff₀ hnR).mp hr
  have hhalf : (I.card:ℝ)≤(n:ℝ)/2 := by linarith
  have hgap : (n:ℝ)/2≤(m:ℝ)-actualK T a0 I := by linarith
  have hd := hdisp T m e f I J he hf hcard hdim ha htau ht x y hw
  have hF := actual_fnorm_rate T I.card (show 2≤n by omega) h0 h1 ha hM
  have hb := finite_budget_rate T I.card m hn0 a0 hhalf hM (actualK T a0 I) rfl hgap
  apply hd.trans
  apply le_trans ?_ hb
  nlinarith

def commonF (a0 : ℝ) := Real.sqrt (Real.exp (1/2)*(32*(scaleCap a0)^2))+2
def gaussianConstant (a0 : ℝ) := commonF a0*displacementConstant a0/(1-(177/184:ℝ)^2)

theorem eventually_gaussian_scaling_rate {A B a0 : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (h0 : 0 ≤ a0) (h1 : a0 < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ (T : Tournament n) (m : ℕ)
      (e f : Fin m ↪ Fin n) (I J : Finset (Fin n)),
      univ.image e=Iᶜ → univ.image f=Jᶜ → J.card=I.card →
      (m:ℝ)=(n:ℝ)-(I.card:ℝ) →
      (∀ i, |normalizedScore T i| ≤ a0) →
      tau (normalizedScore T) ≤ A*Real.log (n:ℝ) →
      (I.card:ℝ) ≤ B*Real.log (n:ℝ) →
      ∀ x y : Fin m → ℝ,
      controlledWitness (actualDeleted T e f I J)
        (density m (16*(scaleCap a0)^2) (actualK T a0 I))
        (residualBudget n m I.card (16*(scaleCap a0)^2) (normalizedMarginalBound T a0) (actualK T a0 I))
        (gapBudget n m (39/46) (actualK T a0 I)) x y →
      ‖RealProjectionAggregationCandidate.g (expScaled (actualDeleted T e f I J) x y-P m)-
        RealProjectionAggregationCandidate.g (center ((realZ T).submatrix e f))‖ ≤
        gaussianConstant a0*rate T I.card := by
  filter_upwards [eventually_ge_atTop 24, eventually_displacement_rate hA hB h0 h1,
    SameRootUniformCapsCandidate.eventually_actual_caps (a0:=a0) hA hB,
    (totalRatio_tendsto A B a0).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/4))]
    with n hn hd hc hratio
  intro T m e f I J he hf hcard hdim ha htau ht x y hw
  have hn0 : 0<n := by omega
  have hnR : (0:ℝ)<n := by exact_mod_cast hn0
  have hk0 : 0≤actualK T a0 I := by
    have hδ := normalizedMarginalBound_nonneg T a0
    unfold actualK
    positivity
  have hr : ((I.card:ℝ)+actualK T a0 I)/(n:ℝ) ≤ 1/4 := by
    rw [add_div]
    exact (add_le_add (div_le_div_of_nonneg_right ht hnR.le)
      (actual_kappaRatio_le hn0 T I hA hB htau ht)).trans hratio.le
  have hs := (div_le_iff₀ hnR).mp hr
  have hmR : (0:ℝ)< m := by linarith
  have hm : 0< m := by exact_mod_cast hmR
  have havg : ActualTwoSidedCenteringCandidate.avg m=P m := by
    ext i j
    simp [ActualTwoSidedCenteringCandidate.avg, P]
  let U := center ((realZ T).submatrix e f)
  let V := expScaled (actualDeleted T e f I J) x y-P m
  have hcaps := hc T I J m e f hm hdim htau ht x y hw
  have hV : ‖V‖≤177/184 := hcaps.2.1
  have hU : ‖U‖≤177/184 := by
    have hz := ActualDeletedCenteredGaussianCandidate.actual_centered_restriction_norm T hn hm e f
    have hz' : ‖U‖≤18/23 := by
      simpa only [U, FiniteCenteredDisplacementCandidate.center, ActualTwoSidedCenteringCandidate.center, havg] using hz
    exact hz'.trans (by norm_num)
  have hFU : fnorm U≤commonF a0 := by
    have hz := (center_fnorm hm ((realZ T).submatrix e f)).trans
      ((restriction_fnorm (realZ T) e f).trans (actual_Z_fnorm T (by omega)))
    exact hz.trans (by unfold commonF; linarith [Real.sqrt_nonneg (Real.exp (1/2)*(32*(scaleCap a0)^2))])
  have hFV : fnorm V≤commonF a0 := by
    have hsq : fnorm V^2 ≤ Real.exp (1/2)*(32*(scaleCap a0)^2) := by
      rw [fnorm_sq]
      exact hcaps.2.2.2
    have hss := Real.sq_sqrt (show 0≤Real.exp (1/2)*(32*(scaleCap a0)^2) by positivity)
    have hfn : 0≤fnorm V := norm_nonneg _
    have hsn := Real.sqrt_nonneg (Real.exp (1/2)*(32*(scaleCap a0)^2))
    unfold commonF
    nlinarith
  have hl := (GaussianDisplacement.gaussian_lipschitz U V (177/184) (commonF a0)
    (by norm_num) (by norm_num) hU hV hFU hFV).2.2
  have hdist : fnorm (V-U)≤displacementConstant a0*rate T I.card :=
    hd T m e f I J he hf hcard hdim ha htau ht x y hw
  change ‖RealProjectionAggregationCandidate.g V-RealProjectionAggregationCandidate.g U‖≤_ at hl
  apply hl.trans
  unfold gaussianConstant
  have hF0 : 0≤commonF a0 := by unfold commonF; positivity
  calc
    _ ≤ commonF a0*(displacementConstant a0*rate T I.card)/(1-(177/184:ℝ)^2) := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hdist hF0) (by norm_num)
    _ = _ := by ring

end ActualSameRootRateCandidate
