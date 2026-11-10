import PhysicalMinorRecoveryCandidate
import ActualPermanentExponentialCandidate
set_option autoImplicit false
noncomputable section
namespace ActualPhysicalExponentialCandidate
open Matrix Finset Filter TournamentHamiltonian ActualTournamentPrescalingBounds
open MatrixScalingMassPotential NonprincipalReconstructionCandidate
open ActualReconstructionBridgeCandidate ActualKappaBridgeCandidate ActualControlledReconstructionCandidate
open ActualPrescalingNormalization DeletedScalingSynthesisCandidate ActualRecoveryUpperCandidate
open PhysicalMinorRecoveryCandidate SameRootPermanentCandidate
open TournamentPrescalingMassBound ActualNormalizedCenteredGapCandidate
open RealProjectionAggregationCandidate SkewBaselineGramDifferenceCandidate
open ActualGaussianFinalRateCandidate ActualSameRootRateCandidate ActualNormalizationRateCandidate
open scoped Topology
/-- An actual independently deleted minor, with its complete Γ and potential,
using one and the same controlled root. No permanent-error assumption remains. -/
theorem eventually_actual_physical_sandwich {A B a0 : ℝ}
    (hA : 0≤A) (hB : 0≤B) (h0 : 0≤a0) (h1 : a0<1) :
    ∀ᶠ n : ℕ in atTop, ∀ (T : Tournament n) (m : ℕ) (I J : Finset (Fin n))
      (r : Fin m ≃ {i // i ∈ Iᶜ}) (c : Fin m ≃ {j // j ∈ Jᶜ}),
      (∀ i,|normalizedScore T i|≤a0) →
      tau (normalizedScore T)≤A*Real.log (n:ℝ) →
      (I.card:ℝ)≤B*Real.log (n:ℝ) →
      let e := complementEmbedding I r
      let f := complementEmbedding J c
      let C := density m (16*(scaleCap a0)^2) (actualK T a0 I)
      let ε := residualBudget n m I.card (16*(scaleCap a0)^2)
        (normalizedMarginalBound T a0) (actualK T a0 I)
      let q := gapBudget n m (39/46) (actualK T a0 I)
      ∃ x y, reconstructedWitness T I J r c C ε q x y ∧
        let R := recoveryFactor T I J m
        let θ := shiftedPotential T I J x y
        let E := (gaussianConstant a0+64)*rate T I.card
        R*Real.exp (-θ)*base m*(Real.exp (g (scaled (signMatrix T))-E)-fixedError a0/(m:ℝ)) ≤
          ((ActualReconstructionBridgeCandidate.adjacency T).submatrix e f).permanent ∧
        ((ActualReconstructionBridgeCandidate.adjacency T).submatrix e f).permanent ≤
          R*Real.exp (-θ)*base m*(Real.exp (g (scaled (signMatrix T))+E)+fixedError a0/(m:ℝ)) := by
  filter_upwards [eventually_ge_atTop 2,
    eventually_actual_reconstruction hA hB h0 h1,
    ActualPermanentExponentialCandidate.eventually_actual_permanent_sandwich hA hB h0 h1,
    SameRootPermanentCandidate.eventually_actual_recovery (a0:=a0) hA hB] with n hn hr hp hdimrec
  intro T m I J r c ha hτ ht
  dsimp only
  obtain ⟨x,y,hw⟩ := hr T m I J r c ha hτ ht
  have hcard := complement_card_eq I J r c
  have hh := hp T m I J r c hcard ha hτ ht x y hw.1
  have hdim := complement_card I r
  have hrem := hdimrec T I J m (complementEmbedding I r) (complementEmbedding J c)
    hdim hτ ht x y hw.1
  have hm : 0 < m := by
    have hnR : (2:ℝ)≤n := by exact_mod_cast hn
    have hmR : (0:ℝ)< m := by linarith [hrem.1]
    exact_mod_cast hmR
  have hb := base_pos hm
  have hR := recoveryFactor_nonnegative T I J m hn h0 h1 ha
  have hfac : 0≤recoveryFactor T I J m*Real.exp (-shiftedPotential T I J x y)*base m :=
    mul_nonneg (mul_nonneg hR (Real.exp_pos _).le) hb.le
  have hident := exact_same_root T I J r c _ _ _ x y hw
  have heq : ((ActualReconstructionBridgeCandidate.adjacency T).submatrix
      (complementEmbedding I r) (complementEmbedding J c)).permanent =
      (recoveryFactor T I J m*Real.exp (-shiftedPotential T I J x y)*base m)*
      ((expScaled (actualDeleted T (complementEmbedding I r) (complementEmbedding J c) I J) x y).permanent/base m) := by
    rw [hident]
    field_simp [ne_of_gt hb]
  refine ⟨x,y,hw,?_,?_⟩
  · rw [heq]
    exact mul_le_mul_of_nonneg_left hh.1 hfac
  · rw [heq]
    exact mul_le_mul_of_nonneg_left hh.2 hfac
end ActualPhysicalExponentialCandidate
#check ActualPhysicalExponentialCandidate.eventually_actual_physical_sandwich
#print axioms ActualPhysicalExponentialCandidate.eventually_actual_physical_sandwich
