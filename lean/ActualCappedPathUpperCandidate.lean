import CappedSpectralConvolutionCandidate
import LogWindowGammaAbsorptionCandidate
import ActualPathFiniteSplitCandidate
import ExceptionalFiniteMarginCandidate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace ActualCappedPathUpperCandidate
open TournamentHamiltonian ActualTournamentPrescalingBounds TournamentPrescalingMassBound
open NonprincipalReconstructionCandidate GeneralScalarRestorationCandidate
open ActualPrincipalBudgetCandidate CappedSpectralConvolutionCandidate
open Filter
open scoped Classical Topology

/-- Actual physical principal minors reindexed to the subtype appearing in the
true path convolution. Both omitted reciprocal products remain present. -/
theorem eventually_actual_principal_subtype_upper {A a0 : ℝ}
    (hA : 0 ≤ A) (h0 : 0 ≤ a0) (h1 : a0 < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ (T : Tournament n) (U : Finset (Fin n)),
      (∀ i, |normalizedScore T i| ≤ a0) →
      tau (normalizedScore T) ≤ A*Real.log (n : ℝ) → (U.card : ℝ) ≤ Real.log (n : ℝ) →
      ((adjacency T).submatrix (Subtype.val : (Uᶜ : Finset (Fin n)) → Fin n) Subtype.val).permanent ≤
        omittedGamma T U U * (((n-U.card).factorial : ℝ)/(2 : ℝ)^(n-U.card)) * gaussianFactor T *
          Real.exp (-1+constant a0*budget n U.card (tau (normalizedScore T))) := by
  filter_upwards [eventually_actual_principal_upper (B := 1) hA (by norm_num) h0 h1]
    with n hp T U ha hτ ht
  let r := subsetVertexEquiv Uᶜ
  have hh := hp T Uᶜ.card U r ha hτ (by simpa using ht)
  have hdim : Uᶜ.card = n-U.card := by simpa using Finset.card_compl U
  change ((ActualReconstructionBridgeCandidate.adjacency T).submatrix
    (fun i => (r i).val) (fun i => (r i).val)).permanent ≤ _ at hh
  rw [ActualPathFiniteSplitCandidate.complement_permanent T U Uᶜ.card r,hdim] at hh
  exact hh

/-- The actual short upper bound preserves a quantitative negative score-energy
factor. No minor upper bound, root, or exponent-budget estimate is a premise. -/
theorem actual_capped_short_upper (A a0 : ℝ) (hA : 0 ≤ A) (h0 : 0 ≤ a0) (h1 : a0 < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ T : Tournament n,
      (∀ i, |normalizedScore T i| ≤ a0) → tau (normalizedScore T) ≤ A*Real.log (n : ℝ) →
      shortConvolution T (subsetCutoff n)/meanPaths n ≤
        spectralRatio T*Real.exp (-tau (normalizedScore T)/2)+C/n := by
  let K := constant a0
  let W := ActualScoreWeightsCandidate.cap a0
  let Ceff := inflation a0 K
  let D := quadraticInflation a0 K
  let c := K+Ceff+D
  let C := 3*Real.exp 1*(c^2+c)
  have hK : 0 ≤ K := constant_nonneg a0
  have hd : 0 < 1-a0^2 := by nlinarith
  have hW : 0 ≤ W := by dsimp [W,ActualScoreWeightsCandidate.cap]; positivity
  have hM1 := weightedPrincipalMoment_nonneg W hW
  have hM2 : 0 ≤ ∑' k, subsetMoment W 2 k := tsum_nonneg (fun k => subsetMoment_nonneg hW 2 k)
  have hCeff : 0 ≤ Ceff := by dsimp [Ceff,inflation]; positivity
  have hD : 0 ≤ D := by dsimp [D,quadraticInflation]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  have hlog := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hinv := tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hxlim := (((hlog.const_mul A).sqrt).add hinv).const_mul K
  simp only [mul_zero,Real.sqrt_zero,add_zero] at hxlim
  have heps : 0 < (2/(K+2) : ℝ) := by positivity
  filter_upwards [hxlim.eventually_le_const (by norm_num : (0 : ℝ) < 1),
    convolution_cutoff_error_eventually_small (2/(K+2)) heps,
    LogWindowGammaAbsorptionCandidate.eventually_actual_absorption A c hc h0 h1,
    eventually_actual_principal_subtype_upper hA h0 h1,
    short_cutoff_eventually_small,eventually_ge_atTop (1 : ℕ)]
    with n hx hk hscore hp hcut hn T ha hτ
  have hnpos : 0 < n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hcutN : 2*subsetCutoff n ≤ n := by
    have hh : (2 : ℝ)*subsetCutoff n ≤ n := by linarith [hcut.2.1,hcut.2.2]
    exact_mod_cast hh
  have hxT : K*(Real.sqrt (tau (normalizedScore T)/n)+1/n) ≤ 1 := by
    change K*(Real.sqrt (A*(Real.log (n : ℝ)/n))+(n : ℝ)⁻¹) ≤ 1 at hx
    have hr := Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hτ hn0.le)
    have heq : (A*Real.log (n : ℝ))/n = A*(Real.log (n : ℝ)/n) := by ring
    rw [heq] at hr
    apply le_trans _ hx
    exact mul_le_mul_of_nonneg_left (add_le_add hr (by simp : (1/(n : ℝ)) ≤ (n : ℝ)⁻¹)) hK
  have hsmall : (K+2)*(subsetCutoff n : ℝ)^2/n ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hk (by positivity : 0 ≤ (K+2)/2)
    convert hh using 1 <;> field_simp
  have hper : ∀ U : Finset (Fin n), U.card < subsetCutoff n →
      ((adjacency T).submatrix (Subtype.val : (Uᶜ : Finset (Fin n)) → Fin n) Subtype.val).permanent ≤
        gamma (normalizedScore T)*(∏ i ∈ U,(1+normalizedScore T i)⁻¹)*
          (∏ j ∈ U,(1-normalizedScore T j)⁻¹)*
            (((n-U.card).factorial : ℝ)/(2 : ℝ)^(n-U.card))*gaussianFactor T*
              Real.exp (-1+K*budget n U.card (tau (normalizedScore T))) := by
    intro U hU
    have ht : (U.card : ℝ) ≤ Real.log (n : ℝ) :=
      (by exact_mod_cast hU.le : (U.card : ℝ) ≤ subsetCutoff n).trans hcut.2.1
    exact hp T U ha hτ ht
  have hshort := finite_spectral_upper T (subsetCutoff n) hn hcutN a0 K h0 h1 hK ha hxT hsmall hper
  let E := K*budget n 0 (tau (normalizedScore T))+
    Ceff*(tau (normalizedScore T)/n+Real.sqrt (tau (normalizedScore T)/n)+1/n)+D/n
  have hE : E ≤ c*SummedGammaAbsorptionCandidate.budget (tau (normalizedScore T)) n :=
    summed_budget_le n (tau (normalizedScore T)) K Ceff D (tau_nonneg _) hK hCeff hD
  have hfactor := hscore T E ha hτ hE
  have hrho := spectralRatio_bounds T hnpos
  have hmul := mul_le_mul_of_nonneg_left hfactor hrho.1.le
  have hmain : shortConvolution T (subsetCutoff n)/meanPaths n ≤
      spectralRatio T*(Real.exp (-tau (normalizedScore T)/2)+Real.exp 1*(c^2+c)/n) := by
    apply hshort.trans
    convert hmul using 1
    dsimp [E,Ceff,D]
    ring
  have herr := mul_le_mul_of_nonneg_right hrho.2
    (by positivity : 0 ≤ Real.exp 1*(c^2+c)/(n : ℝ))
  apply hmain.trans
  dsimp [C]
  convert add_le_add (le_refl (spectralRatio T*Real.exp (-tau (normalizedScore T)/2))) herr using 1 <;> ring

/-- The true long tail is added absolutely, after all Gamma absorption. -/
theorem actual_capped_path_upper (A a0 : ℝ) (hA : 0 ≤ A) (h0 : 0 ≤ a0) (h1 : a0 < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ T : Tournament n,
      (∀ i, |normalizedScore T i| ≤ a0) → tau (normalizedScore T) ≤ A*Real.log (n : ℝ) →
      (pathCount T : ℝ)/meanPaths n ≤ spectralRatio T*Real.exp (-tau (normalizedScore T)/2)+C/n := by
  obtain ⟨C,hC,hshort⟩ := actual_capped_short_upper A a0 hA h0 h1
  refine ⟨C+1,by linarith,?_⟩
  filter_upwards [hshort,longConvolution_eventually_small (ε := 1) (by norm_num)]
    with n hs hl T ha hτ
  rw [← shortConvolution_add_longConvolution T (subsetCutoff n),add_div]
  have hh := add_le_add (hs T ha hτ) (hl T)
  convert hh using 1
  ring

/-- Weaker comparison retained as a corollary; it does not identify the
spectral maximum with the separate reference constant L. -/
theorem actual_capped_path_upper_weak (A a0 : ℝ) (hA : 0 ≤ A) (h0 : 0 ≤ a0) (h1 : a0 < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ T : Tournament n,
      (∀ i, |normalizedScore T i| ≤ a0) → tau (normalizedScore T) ≤ A*Real.log (n : ℝ) →
      (pathCount T : ℝ)/meanPaths n ≤ spectralRatio T+C/n := by
  obtain ⟨C,hC,hupper⟩ := actual_capped_path_upper A a0 hA h0 h1
  refine ⟨C,hC,?_⟩
  filter_upwards [hupper,eventually_gt_atTop 0] with n hu hn T ha hτ
  have he : Real.exp (-tau (normalizedScore T)/2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith [tau_nonneg (normalizedScore T)])
  have hh := mul_le_mul_of_nonneg_left he (spectralRatio_bounds T hn).1.le
  exact (hu T ha hτ).trans (by simpa only [mul_one] using add_le_add hh (le_refl (C/(n : ℝ))))

end ActualCappedPathUpperCandidate

set_option pp.fullNames true
#check ActualCappedPathUpperCandidate.eventually_actual_principal_subtype_upper
#print axioms ActualCappedPathUpperCandidate.eventually_actual_principal_subtype_upper
#check ActualCappedPathUpperCandidate.actual_capped_short_upper
#print axioms ActualCappedPathUpperCandidate.actual_capped_short_upper
#check ActualCappedPathUpperCandidate.actual_capped_path_upper
#print axioms ActualCappedPathUpperCandidate.actual_capped_path_upper
#check ActualCappedPathUpperCandidate.actual_capped_path_upper_weak
#print axioms ActualCappedPathUpperCandidate.actual_capped_path_upper_weak
