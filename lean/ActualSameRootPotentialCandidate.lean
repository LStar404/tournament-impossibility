import SameRootPotentialCandidate
import ActualTournamentDisplacementCandidate
/-! Verified isolated actual endpoint. Same supplied witness, no potential premise. -/
set_option autoImplicit false
noncomputable section
namespace ActualSameRootPotentialCandidate
open Matrix Finset Filter
open scoped Topology
open TournamentHamiltonian ActualTournamentPrescalingBounds ActualPrescalingNormalization
open TournamentPrescalingMassBound DeletedScalingSynthesisCandidate LogWindowDeletionBudgetCandidate
open ActualReconstructionBridgeCandidate ActualKappaBridgeCandidate
open SameRootPotentialCandidate ActualTournamentDisplacementCandidate
open MatrixScalingMassPotential LogWindowFrobeniusUniformCandidate

theorem eventually_actual_potential {A B a0 : ℝ}
    (hA : 0≤A) (hB : 0≤B) (h0 : 0≤a0) (h1 : a0<1) :
    ∀ᶠ n : ℕ in atTop, ∀ (T : Tournament n) (m : ℕ) (I J : Finset (Fin n))
      (r : Fin m ≃ {i // i∈Iᶜ}) (c : Fin m ≃ {j // j∈Jᶜ}),
      (∀ i, |normalizedScore T i|≤a0) →
      tau (normalizedScore T)≤A*Real.log (n:ℝ) → (I.card:ℝ)≤B*Real.log (n:ℝ) →
      let C := density m (16*(scaleCap a0)^2) (actualK T a0 I)
      let ε := residualBudget n m I.card (16*(scaleCap a0)^2) (normalizedMarginalBound T a0) (actualK T a0 I)
      let q := gapBudget n m (39/46) (actualK T a0 I)
      ∀ x y : Fin m → ℝ,
      controlledWitness (actualDeleted T (complementEmbedding I r) (complementEmbedding J c) I J) C ε q x y →
      0≤theta x y ∧ theta x y≤(2*Real.exp (1/2)/(7/184))*(m:ℝ)*ε^2 := by
  filter_upwards [eventually_ge_atTop 2, eventually_remaining_budgets (a0:=a0) hA hB,
    (totalRatio_tendsto A B a0).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<7/92))]
    with n hn hb hz
  intro T m I J r c ha htau ht
  dsimp only
  intro x y hw
  have hn0 : 0<n := by omega
  have hnR : (0:ℝ)<n := by exact_mod_cast hn0
  have hdim := complement_card I r
  have hcard := ActualControlledReconstructionCandidate.complement_card_eq I J r c
  have hbudget := hb T I m hdim htau ht
  have hk0 : 0≤actualK T a0 I := by
    have hδ := normalizedMarginalBound_nonneg T a0
    unfold actualK
    positivity
  have hratio : (I.card:ℝ)/(n:ℝ)+actualK T a0 I/(n:ℝ)≤7/92 :=
    (add_le_add (div_le_div_of_nonneg_right ht hnR.le)
      (actual_kappaRatio_le hn0 T I hA hB htau ht)).trans hz.le
  have hsum : (I.card:ℝ)+actualK T a0 I≤(7/92)*(n:ℝ) := by
    exact (div_le_iff₀ hnR).mp (by simpa only [add_div] using hratio)
  have hm : 0 < m := by
    have hmR : (0:ℝ)< m := by linarith
    exact_mod_cast hmR
  have hhalf : 2*I.card≤n := by
    have hh : (2:ℝ)*(I.card:ℝ)≤n := by linarith
    exact_mod_cast hh
  have hk := actual_independent_deletion_bound T hn h0 h1 ha I J hcard hhalf
  have hpos : 0<(m:ℝ)+IndependentDeletionMass.deletionExcess (normalizedMatrix T) I J := by
    have hkl := (abs_le.mp hk).1
    change -actualK T a0 I ≤ _ at hkl
    linarith [hbudget.1]
  have hmass := actual_deleted_mass T I J r c hm hpos.ne'
  have hmarg := actual_deleted_marginals T hn (complementEmbedding I r) (complementEmbedding J c)
    I J (ActualControlledReconstructionCandidate.complement_image I r)
    (ActualControlledReconstructionCandidate.complement_image J c) hcard hdim hhalf h0 h1 ha hbudget.1
  have hC : 0≤density m (16*(scaleCap a0)^2) (actualK T a0 I) := by
    unfold density
    have hh := sub_pos.mpr hbudget.1
    positivity
  have hε : 0≤residualBudget n m I.card (16*(scaleCap a0)^2) (normalizedMarginalBound T a0) (actualK T a0 I) := by
    unfold residualBudget
    have hh := sub_pos.mpr hbudget.1
    have hδ := normalizedMarginalBound_nonneg T a0
    positivity
  have he := deletion_envelopes hn0 hdim (Nat.cast_nonneg I.card)
    (show 0≤16*(scaleCap a0)^2 by positivity) hratio
  have hthreshold := threshold_radius hC hbudget.2.1 hbudget.2.2
  have hden : (7/184:ℝ)≤1-gapBudget n m (39/46) (actualK T a0 I)-
      4*residualBudget n m I.card (16*(scaleCap a0)^2) (normalizedMarginalBound T a0) (actualK T a0 I) := by
    linarith [he.2,hthreshold.2.2]
  have hY : ∀ i j,0≤actualDeleted T (complementEmbedding I r) (complementEmbedding J c) I J i j := by
    intro i j
    have hs := (hw.2.2.2.2.1 i j).1
    change 0≤actualDeleted T (complementEmbedding I r) (complementEmbedding J c) I J i j*
      Real.exp (x i+y j) at hs
    exact nonneg_of_mul_nonneg_left hs (Real.exp_pos _)
  have hpot := same_root_potential _ x y hw hY hmass hε (by linarith) hmarg.1 hmarg.2
  have hD : Real.exp (2*RawScalingSynthesis.radius
      (density m (16*(scaleCap a0)^2) (actualK T a0 I))
      (gapBudget n m (39/46) (actualK T a0 I))
      (residualBudget n m I.card (16*(scaleCap a0)^2) (normalizedMarginalBound T a0) (actualK T a0 I)))/
      (1-gapBudget n m (39/46) (actualK T a0 I)-4*residualBudget n m I.card
        (16*(scaleCap a0)^2) (normalizedMarginalBound T a0) (actualK T a0 I)) ≤ Real.exp (1/2)/(7/184) := by
    apply div_le_div₀ (by positivity)
    · exact Real.exp_le_exp.mpr (by linarith [hthreshold.2.1])
    · norm_num
    · exact hden
  refine ⟨hpot.1,?_⟩
  have hh := mul_le_mul_of_nonneg_right hD
    (show 0≤2*(m:ℝ)*(residualBudget n m I.card (16*(scaleCap a0)^2)
      (normalizedMarginalBound T a0) (actualK T a0 I))^2 by positivity)
  nlinarith [hpot.2.2]
end ActualSameRootPotentialCandidate
