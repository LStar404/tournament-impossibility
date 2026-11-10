import ActualSameRootRateCandidate
import DeletedCenteredGaussianRateCandidate
/-! Isolated finite rate proof. Actual determinant-log final rate only. -/
set_option autoImplicit false
noncomputable section
namespace ActualGaussianFinalRateCandidate
open Matrix Finset Filter
open scoped Topology Matrix.Norms.L2Operator
open TournamentHamiltonian ActualTournamentPrescalingBounds ActualPrescalingNormalization
open TournamentPrescalingMassBound DeletedScalingSynthesisCandidate LogWindowDeletionBudgetCandidate
open ActualReconstructionBridgeCandidate ActualHessianFinite MatrixScalingMassPotential
open ActualDeletedCenteredGaussianCandidate ActualNormalizationRateCandidate ActualSameRootRateCandidate
open RealProjectionAggregationCandidate SkewBaselineGramDifferenceCandidate

lemma retained_image {n m : ℕ} (I : Finset (Fin n))
    (r : Fin m ≃ {i // i∈Iᶜ}) : univ.image (retainedEmbedding I r)=Iᶜ := by
  ext i
  constructor
  · intro hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact (r j).property
  · intro hi
    refine Finset.mem_image.mpr ⟨r.symm ⟨i,hi⟩, Finset.mem_univ _, ?_⟩
    change (r (r.symm ⟨i,hi⟩)).val=i
    rw [r.apply_symm_apply]

/-- Actual final Gaussian comparison, uniform on fixed score/log windows.
Every supplied controlled scaling root is preserved, including its Gamma identity. -/
theorem eventually_actual_gaussian_rate {A B a0 : ℝ}
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
      ‖g (expScaled (actualDeleted T (retainedEmbedding I r) (retainedEmbedding J c) I J) x y-P m)-
        g (scaled (signMatrix T))‖ ≤ (gaussianConstant a0+64)*rate T I.card := by
  filter_upwards [eventually_ge_atTop 24, eventually_gaussian_scaling_rate hA hB h0 h1,
    (deletionRatio_tendsto B).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))]
    with n hn hg htmax
  intro T m I J r c hcard ha htau ht x y hw
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hdim : (m:ℝ)=(n:ℝ)-(I.card:ℝ) := by
    have hnat := retained_card_relation I r I.card rfl
    have hreal : (n:ℝ)=(m:ℝ)+(I.card:ℝ) := by exact_mod_cast hnat
    linarith
  have hratio : (I.card:ℝ)/(n:ℝ)≤1/2 :=
    (div_le_div_of_nonneg_right ht hnR.le).trans htmax.le
  have hhalf : (n:ℝ)/2≤(m:ℝ) := by
    have hh := (div_le_iff₀ hnR).mp hratio
    linarith
  have hscale := hg T m (retainedEmbedding I r) (retainedEmbedding J c) I J
    (retained_image I r) (retained_image J c) hcard hdim ha htau ht x y hw
  have hbase := DeletedCenteredGaussianRateCandidate.actual_independent_centered_rate
    T hn hhalf I J r c I.card rfl hcard
  dsimp only at hbase
  have havg : ActualTwoSidedCenteringCandidate.avg m=P m := by
    ext i j
    simp [ActualTwoSidedCenteringCandidate.avg, P]
  simp only [ActualTwoSidedCenteringCandidate.center, havg] at hbase
  change ‖g (FiniteCenteredDisplacementCandidate.center
      ((IndependentCenteringEnergyCandidate.realZ T).submatrix (retainedEmbedding I r) (retainedEmbedding J c)))-
      g (scaled (signMatrix T))‖ ≤64*rate T I.card at hbase
  calc
    _ ≤ ‖g (expScaled (actualDeleted T (retainedEmbedding I r) (retainedEmbedding J c) I J) x y-P m)-
          g (FiniteCenteredDisplacementCandidate.center ((IndependentCenteringEnergyCandidate.realZ T).submatrix
            (retainedEmbedding I r) (retainedEmbedding J c)))‖+
        ‖g (FiniteCenteredDisplacementCandidate.center ((IndependentCenteringEnergyCandidate.realZ T).submatrix
            (retainedEmbedding I r) (retainedEmbedding J c)))-g (scaled (signMatrix T))‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ gaussianConstant a0*rate T I.card+64*rate T I.card := add_le_add hscale hbase
    _ = _ := by ring
end ActualGaussianFinalRateCandidate
