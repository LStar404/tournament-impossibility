import GaussianExponentialCandidate
/-! Isolated finite rate proof. Actual determinant-log final rate only. -/
set_option autoImplicit false
noncomputable section
namespace ActualGaussianMainCandidate
open Matrix Finset Filter
open scoped Topology Matrix.Norms.L2Operator
open TournamentHamiltonian ActualTournamentPrescalingBounds ActualPrescalingNormalization
open TournamentPrescalingMassBound DeletedScalingSynthesisCandidate LogWindowDeletionBudgetCandidate
open ActualReconstructionBridgeCandidate ActualHessianFinite MatrixScalingMassPotential
open ActualDeletedCenteredGaussianCandidate ActualNormalizationRateCandidate ActualSameRootRateCandidate
open RealProjectionAggregationCandidate SkewBaselineGramDifferenceCandidate

open ActualGaussianFinalRateCandidate GaussianExponentialCandidate

theorem eventually_actual_main_sandwich {A B a0 : ℝ}
    (hA : 0≤A) (hB : 0≤B) (h0 : 0≤a0) (h1 : a0<1) :
    ∀ᶠ n : ℕ in atTop, ∀ (T : Tournament n) (m : ℕ) (I J : Finset (Fin n))
      (r : Fin m ≃ {i // i∈Iᶜ}) (c : Fin m ≃ {j // j∈Jᶜ}),
      J.card=I.card → (∀ i, |normalizedScore T i|≤a0) →
      tau (normalizedScore T)≤A*Real.log (n:ℝ) → (I.card:ℝ)≤B*Real.log (n:ℝ) →
      ∀ x y : Fin m → ℝ,
      controlledWitness (actualDeleted T (retainedEmbedding I r) (retainedEmbedding J c) I J)
        (density m (16*(scaleCap a0)^2) (actualK T a0 I))
        (residualBudget n m I.card (16*(scaleCap a0)^2) (normalizedMarginalBound T a0) (actualK T a0 I))
        (gapBudget n m (39/46) (actualK T a0 I)) x y →
      let W := expScaled (actualDeleted T (retainedEmbedding I r) (retainedEmbedding J c) I J) x y-P m
      let E := (gaussianConstant a0+64)*rate T I.card
      0<(1-Wᵀ*W).det ∧
      (Real.sqrt (1-Wᵀ*W).det)⁻¹=Real.exp (g W) ∧
      Real.exp (g (scaled (signMatrix T))-E)≤(Real.sqrt (1-Wᵀ*W).det)⁻¹ ∧
      (Real.sqrt (1-Wᵀ*W).det)⁻¹≤Real.exp (g (scaled (signMatrix T))+E) := by
  filter_upwards [eventually_ge_atTop 24, eventually_actual_gaussian_rate hA hB h0 h1,
    SameRootUniformCapsCandidate.eventually_actual_caps (a0:=a0) hA hB,
    (deletionRatio_tendsto B).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))]
    with n hn hg hc htmax
  intro T m I J r c hcard ha htau ht x y hw
  dsimp only
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hdim : (m:ℝ)=(n:ℝ)-(I.card:ℝ) := by
    have hnat := retained_card_relation I r I.card rfl
    have hreal : (n:ℝ)=(m:ℝ)+(I.card:ℝ) := by exact_mod_cast hnat
    linarith
  have hratio : (I.card:ℝ)/(n:ℝ)≤1/2 :=
    (div_le_div_of_nonneg_right ht hnR.le).trans htmax.le
  have hm : 0 < m := by
    have hh := (div_le_iff₀ hnR).mp hratio
    have hmR : (0:ℝ)< m := by linarith
    exact_mod_cast hmR
  let W := expScaled (actualDeleted T (retainedEmbedding I r) (retainedEmbedding J c) I J) x y-P m
  have hcaps := hc T I J m (retainedEmbedding I r) (retainedEmbedding J c)
    hm hdim htau ht x y hw
  have hW : ‖W‖≤177/184 := hcaps.2.1
  have hpos := GaussianDisplacement.gram_det_pos W (177/184) (by norm_num) (by norm_num) hW
  have heq := gaussian_main_eq_exp W hpos
  have hdiff := hg T m I J r c hcard ha htau ht x y hw
  have hs := exp_sandwich hdiff
  refine ⟨hpos, heq, ?_, ?_⟩
  · rw [heq]
    exact hs.1
  · rw [heq]
    exact hs.2
end ActualGaussianMainCandidate
