import UnitScorePotentialBudgetCandidate
set_option autoImplicit false
noncomputable section
namespace ActualUnitScorePrefactorCandidate
open Matrix Finset Filter
open scoped Topology
open TournamentHamiltonian ActualTournamentPrescalingBounds ActualPrescalingNormalization
open TournamentPrescalingMassBound DeletedScalingSynthesisCandidate LogWindowDeletionBudgetCandidate
open ActualReconstructionBridgeCandidate ActualKappaBridgeCandidate ActualControlledReconstructionCandidate
open SameRootPotentialCandidate ActualSameRootPotentialCandidate MatrixScalingMassPotential
open UnitScorePrefactorCandidate UnitScoreEnvelopesCandidate UnitScoreLogFactorCandidate
open UnitScorePotentialBudgetCandidate PhysicalMinorRecoveryCandidate

theorem eventually_unit_prefactor {B : ℝ} (hB : 0≤B) :
    ∀ᶠ n : ℕ in atTop, ∀ (T : Tournament n) (m : ℕ) (I : Finset (Fin n))
      (r : Fin m ≃ {i // i∈Iᶜ}),
      (∀ i, |score T i|≤1) → (I.card:ℝ)≤B*Real.log (n:ℝ) →
      let C := density m (16*(scaleCap (1/2))^2) (actualK T (1/2) I)
      let ε := residualBudget n m I.card (16*(scaleCap (1/2))^2)
        (normalizedMarginalBound T (1/2)) (actualK T (1/2) I)
      let q := gapBudget n m (39/46) (actualK T (1/2) I)
      ∀ x y : Fin m → ℝ,
      controlledWitness (actualDeleted T (complementEmbedding I r) (complementEmbedding I r) I I) C ε q x y →
      |shiftedPotential T I I x y|≤thetaConstant*((I.card:ℝ)+1)^2/(n:ℝ) ∧
      0<fullPrefactor T I x y ∧
      |Real.log (fullPrefactor T I x y)|≤fullConstant*((I.card:ℝ)+1)^2/(n:ℝ) ∧
      Real.exp (-fullConstant*((I.card:ℝ)+1)^2/(n:ℝ))≤fullPrefactor T I x y ∧
      fullPrefactor T I x y≤Real.exp (fullConstant*((I.card:ℝ)+1)^2/(n:ℝ)) := by
  have hlog : ∀ᶠ n : ℕ in atTop, (1:ℝ)≤Real.log (n:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  filter_upwards [eventually_ge_atTop 16, hlog,
    eventually_actual_potential (A:=4) (B:=B) (a0:=1/2) (by norm_num) hB (by norm_num) (by norm_num),
    (totalRatio_tendsto 4 B (1/2)).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/4))]
    with n hn hlog hp hz
  intro T m I r hs ht
  dsimp only
  intro x y hw
  have hn4 : 4≤n := by omega
  have hn0 : 0<n := by omega
  have hnR : (0:ℝ)<n := by exact_mod_cast hn0
  have hcaps := unit_score_caps T hn4 hs
  have hτ : tau (normalizedScore T)≤4*Real.log (n:ℝ) := by linarith [hcaps.2.2.2]
  have hdim := complement_card I r
  have hmle : m≤n := by
    have hmR : (m:ℝ)≤n := by linarith [show (0:ℝ)≤(I.card:ℝ) from Nat.cast_nonneg _]
    exact_mod_cast hmR
  have hk0 : 0≤actualK T (1/2) I := by
    have hδ := normalizedMarginalBound_nonneg T (1/2)
    unfold actualK
    positivity
  have hratio : ((I.card:ℝ)+actualK T (1/2) I)/(n:ℝ)≤1/4 := by
    rw [add_div]
    exact (add_le_add (div_le_div_of_nonneg_right ht hnR.le)
      (actual_kappaRatio_le hn0 T I (by norm_num : (0:ℝ)≤4) hB hτ ht)).trans hz.le
  have hsum := (div_le_iff₀ hnR).mp hratio
  have hgap : (n:ℝ)/2≤(m:ℝ)-actualK T (1/2) I := by linarith
  have hhalf : (I.card:ℝ)≤(n:ℝ)/2 := by linarith
  have hhalfN : 2*I.card≤n := by exact_mod_cast (show (2:ℝ)*(I.card:ℝ)≤n by linarith)
  have hmR : (0:ℝ)< m := by linarith
  have hsmall : actualK T (1/2) I<(m:ℝ) := by linarith
  have he0 : 0≤residualBudget n m I.card (16*(scaleCap (1/2))^2)
      (normalizedMarginalBound T (1/2)) (actualK T (1/2) I) := by
    unfold residualBudget
    have hden := sub_pos.mpr hsmall
    have hδ := normalizedMarginalBound_nonneg T (1/2)
    positivity
  have hk := actual_independent_deletion_bound T (by omega) (by norm_num : (0:ℝ)≤1/2)
    (by norm_num) hcaps.2.1 I I rfl hhalfN
  change |IndependentDeletionMass.deletionExcess (normalizedMatrix T) I I|≤actualK T (1/2) I at hk
  have hb := unit_deletion_budgets T hn4 hs I m hhalf hgap
  have hpot := hp T m I I r r hcaps.2.1 hτ ht x y hw
  have hθ : |shiftedPotential T I I x y|≤thetaConstant*((I.card:ℝ)+1)^2/(n:ℝ) := by
    rw [exact_shift]
    exact finite_theta_budget hnR hmR (by exact_mod_cast hmle) (Nat.cast_nonneg I.card)
      he0 hb.2 (hk.trans hb.1) (hk.trans (by linarith [show (m:ℝ)≤n by exact_mod_cast hmle]))
      hpot.1 hpot.2
  have hF := full_log_bound T hn hs I x y hmle
  have hlogF : |Real.log (fullPrefactor T I x y)|≤fullConstant*((I.card:ℝ)+1)^2/(n:ℝ) := by
    have hi : (0:ℝ)≤(n:ℝ)⁻¹ := inv_nonneg.mpr hnR.le
    have ht0 : (0:ℝ)≤I.card := Nat.cast_nonneg _
    have hsq : (1:ℝ)≤((I.card:ℝ)+1)^2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_right hsq hi
    unfold fullConstant
    simp only [div_eq_mul_inv] at hθ hF ⊢
    nlinarith [hF.2]
  refine ⟨hθ,hF.1,hlogF,?_,?_⟩
  · rw [← Real.exp_log hF.1]
    apply Real.exp_le_exp.mpr
    have hh := (abs_le.mp hlogF).1
    simpa only [neg_div, neg_mul] using hh
  · rw [← Real.exp_log hF.1]
    exact Real.exp_le_exp.mpr (abs_le.mp hlogF).2
end ActualUnitScorePrefactorCandidate
