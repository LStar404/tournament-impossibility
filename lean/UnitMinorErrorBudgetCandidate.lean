import SignedMinorScalarCandidate
import ActualPrincipalPathRecoveryCandidate
set_option autoImplicit false
noncomputable section
namespace UnitMinorErrorBudgetCandidate
open Filter
open scoped Topology
open TournamentHamiltonian ActualTournamentPrescalingBounds TournamentPrescalingMassBound
open UnitScoreEnvelopesCandidate UnitScorePotentialBudgetCandidate
open ActualSameRootRateCandidate ActualNormalizationRateCandidate SameRootPermanentCandidate

def lowerConstant : ℝ := fullConstant+2+3*(gaussianConstant (1/2)+64)+2*Real.exp 2*|fixedError (1/2)|

lemma constants_nonneg : 0≤fullConstant ∧ 0≤gaussianConstant (1/2)+64 ∧ 0≤lowerConstant := by
  have hf : 0≤fullConstant := by unfold fullConstant thetaConstant; positivity
  have hg : 0≤gaussianConstant (1/2)+64 := by
    unfold gaussianConstant commonF displacementConstant deltaConstant
    positivity
  refine ⟨hf,hg,?_⟩
  unfold lowerConstant
  positivity

lemma eventual_short_small :
    ∀ᶠ n : ℕ in atTop, fullConstant*(Real.log (n:ℝ)+1)^2/(n:ℝ)≤1 := by
  have h0 : Tendsto (fun n : ℕ => (1:ℝ)/(n:ℝ)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun n : ℕ => Real.log (n:ℝ)/(n:ℝ)) atTop (𝓝 0) := by
    simpa using LogWindowErrorCandidate.log_power_decay 1 (by norm_num : (0:ℝ)<1)
  have h2 : Tendsto (fun n : ℕ => (Real.log (n:ℝ))^2/(n:ℝ)) atTop (𝓝 0) := by
    simpa using LogWindowErrorCandidate.log_power_decay 2 (by norm_num : (0:ℝ)<1)
  have hh := (((h2.add (h1.const_mul 2)).add h0).const_mul fullConstant)
  have ht : Tendsto (fun n : ℕ => fullConstant*(Real.log (n:ℝ)+1)^2/(n:ℝ)) atTop (𝓝 0) := by
    convert hh using 1
    · funext n; ring
    · simp
  exact (ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))).mono (fun n hn => hn.le)

lemma rate_budget {n : ℕ} (T : Tournament n) (hn : 4≤n)
    (hs : ∀ i, |score T i|≤1) (k : ℕ) :
    (gaussianConstant (1/2)+64)*rate T k ≤
      (3*(gaussianConstant (1/2)+64))*((k:ℝ)+1)^2/(n:ℝ) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hh := unit_sqrt_ratio T hn hs
  rw [← Real.sqrt_div (tau_nonneg _)] at hh
  have ht : (k:ℝ)+3≤3*((k:ℝ)+1)^2 := by nlinarith [Nat.cast_nonneg (α:=ℝ) k]
  have ht' := div_le_div_of_nonneg_right ht hnR.le
  have hr : rate T k≤3*((k:ℝ)+1)^2/(n:ℝ) := by
    unfold rate
    simp only [div_eq_mul_inv] at hh ht' ⊢
    linarith
  have hb := mul_le_mul_of_nonneg_left hr constants_nonneg.2.1
  convert hb using 1 ; ring
end UnitMinorErrorBudgetCandidate
