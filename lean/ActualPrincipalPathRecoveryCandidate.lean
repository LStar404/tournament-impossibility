import ActualPhysicalExponentialCandidate
import ActualPathFiniteSplitCandidate
set_option autoImplicit false
noncomputable section
namespace ActualPrincipalPathRecoveryCandidate
open Matrix Finset Filter TournamentHamiltonian ActualTournamentPrescalingBounds
open MatrixScalingMassPotential NonprincipalReconstructionCandidate
open ActualReconstructionBridgeCandidate ActualKappaBridgeCandidate ActualControlledReconstructionCandidate
open ActualPrescalingNormalization DeletedScalingSynthesisCandidate ActualRecoveryUpperCandidate
open PhysicalMinorRecoveryCandidate SameRootPermanentCandidate
open TournamentPrescalingMassBound ActualNormalizedCenteredGapCandidate
open RealProjectionAggregationCandidate SkewBaselineGramDifferenceCandidate
open ActualGaussianFinalRateCandidate ActualSameRootRateCandidate ActualNormalizationRateCandidate
open scoped Topology
theorem eventually_actual_principal_sandwich {A B a0 : ℝ}
    (hA : 0≤A) (hB : 0≤B) (h0 : 0≤a0) (h1 : a0<1) :
    ∀ᶠ n : ℕ in atTop, ∀ (T : Tournament n) (m : ℕ) (U : Finset (Fin n))
      (r : Fin m ≃ {i // i ∈ Uᶜ}),
      (∀ i,|normalizedScore T i|≤a0) →
      tau (normalizedScore T)≤A*Real.log (n:ℝ) →
      (U.card:ℝ)≤B*Real.log (n:ℝ) →
      let C := density m (16*(scaleCap a0)^2) (actualK T a0 U)
      let ε := residualBudget n m U.card (16*(scaleCap a0)^2)
        (normalizedMarginalBound T a0) (actualK T a0 U)
      let q := gapBudget n m (39/46) (actualK T a0 U)
      ∃ x y, reconstructedWitness T U U r r C ε q x y ∧
        let R := recoveryFactor T U U m
        let θ := shiftedPotential T U U x y
        let E := (gaussianConstant a0+64)*rate T U.card
        R*Real.exp (-θ)*base m*(Real.exp (g (scaled (signMatrix T))-E)-fixedError a0/(m:ℝ)) ≤
          ((TournamentHamiltonian.adjacency T).submatrix
            (Subtype.val : (Uᶜ : Finset (Fin n)) → Fin n) Subtype.val).permanent ∧
        ((TournamentHamiltonian.adjacency T).submatrix
            (Subtype.val : (Uᶜ : Finset (Fin n)) → Fin n) Subtype.val).permanent ≤
          R*Real.exp (-θ)*base m*(Real.exp (g (scaled (signMatrix T))+E)+fixedError a0/(m:ℝ)) := by
  filter_upwards [ActualPhysicalExponentialCandidate.eventually_actual_physical_sandwich hA hB h0 h1] with n hp
  intro T m U r ha hτ ht
  dsimp only
  obtain ⟨x,y,hw,hl,hu⟩ := hp T m U U r r ha hτ ht
  have heq : ((ActualReconstructionBridgeCandidate.adjacency T).submatrix
      (complementEmbedding U r) (complementEmbedding U r)).permanent =
      ((TournamentHamiltonian.adjacency T).submatrix
        (Subtype.val : (Uᶜ : Finset (Fin n)) → Fin n) Subtype.val).permanent :=
    ActualPathFiniteSplitCandidate.complement_permanent T U m r
  rw [heq] at hl hu
  exact ⟨x,y,hw,hl,hu⟩
end ActualPrincipalPathRecoveryCandidate
