import ActualGaussianMainCandidate
import SameRootPermanentCandidate
/-! Isolated finite rate proof. Actual determinant-log final rate only. -/
set_option autoImplicit false
noncomputable section
namespace ActualPermanentExponentialCandidate
open Matrix Finset Filter
open scoped Topology Matrix.Norms.L2Operator
open TournamentHamiltonian ActualTournamentPrescalingBounds ActualPrescalingNormalization
open TournamentPrescalingMassBound DeletedScalingSynthesisCandidate LogWindowDeletionBudgetCandidate
open ActualReconstructionBridgeCandidate ActualHessianFinite MatrixScalingMassPotential
open ActualDeletedCenteredGaussianCandidate ActualNormalizationRateCandidate ActualSameRootRateCandidate
open RealProjectionAggregationCandidate SkewBaselineGramDifferenceCandidate

open ActualGaussianFinalRateCandidate GaussianExponentialCandidate

open ActualGaussianMainCandidate

theorem eventually_actual_permanent_sandwich {A B a0 : ℝ}
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
      let M := expScaled (actualDeleted T (retainedEmbedding I r) (retainedEmbedding J c) I J) x y
      let E := (gaussianConstant a0+64)*rate T I.card
      Real.exp (g (scaled (signMatrix T))-E)-SameRootPermanentCandidate.fixedError a0/(m:ℝ) ≤
        M.permanent/((m.factorial:ℝ)/(m:ℝ)^m) ∧
      M.permanent/((m.factorial:ℝ)/(m:ℝ)^m) ≤
        Real.exp (g (scaled (signMatrix T))+E)+SameRootPermanentCandidate.fixedError a0/(m:ℝ) := by
  filter_upwards [eventually_actual_main_sandwich hA hB h0 h1,
    SameRootPermanentCandidate.eventually_actual_recovery (a0:=a0) hA hB] with n hg hp
  intro T m I J r c hcard ha htau ht x y hw
  dsimp only
  have hdim : (m:ℝ)=(n:ℝ)-(I.card:ℝ) := by
    have hnat := retained_card_relation I r I.card rfl
    have hreal : (n:ℝ)=(m:ℝ)+(I.card:ℝ) := by exact_mod_cast hnat
    linarith
  have hmain := hg T m I J r c hcard ha htau ht x y hw
  have hrec := hp T I J m (retainedEmbedding I r) (retainedEmbedding J c) hdim htau ht x y hw
  exact approximate_main_sandwich hrec.2.2.1 hmain.2.2
end ActualPermanentExponentialCandidate
