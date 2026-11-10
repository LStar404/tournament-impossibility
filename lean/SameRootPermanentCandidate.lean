import SameRootUniformCapsCandidate
import GeneralBalancedPermanent

/-! Zeroth-order recovery for the same supplied root of the actual deleted matrix. -/
set_option autoImplicit false
noncomputable section
namespace SameRootPermanentCandidate
open Matrix Finset Filter
open scoped Topology
open ActualHessianFinite MatrixScalingMassPotential ActualReconstructionBridgeCandidate
open SameRootUniformCapsCandidate LogWindowFrobeniusUniformCandidate
open TournamentHamiltonian ActualTournamentPrescalingBounds ActualPrescalingNormalization
open DeletedScalingSynthesisCandidate LogWindowDeletionBudgetCandidate TournamentPrescalingMassBound

/-- The density cap is independent of the tournament, deletion, root and dimension. -/
def fixedDensity (a0 : ℝ) : ℝ := Real.exp (1/2)*(32*(scaleCap a0)^2)

def fixedError (a0 : ℝ) : ℝ :=
  GeneralZerothTail.globalConstant (fixedDensity a0) (177/184)

lemma fixedDensity_nonneg (a0 : ℝ) : 0 ≤ fixedDensity a0 := by
  unfold fixedDensity
  positivity

/-- The density is derived for the supplied witness; no second root is chosen. -/
lemma same_root_density {m : ℕ} (hm : 0 < m) (Y : Matrix (Fin m) (Fin m) ℝ)
    (x y : Fin m → ℝ) {C ε q Cstar : ℝ}
    (hw : controlledWitness Y C ε q x y)
    (hC : 0 ≤ C) (hCs : C ≤ Cstar) (hq : q ≤ 85/92)
    (ht : ε ≤ RawScalingSynthesis.epsilonThreshold C q) :
    ∀ i j, 0 ≤ expScaled Y x y i j ∧
      expScaled Y x y i j ≤ (Real.exp (1/2)*Cstar)/(m : ℝ) := by
  have hradius := (threshold_radius hC (show q < 1 by linarith) ht).2.1
  have hcstar : 0 ≤ Cstar := hC.trans hCs
  intro i j
  refine ⟨(hw.2.2.2.2.1 i j).1, (hw.2.2.2.2.1 i j).2.trans ?_⟩
  rw [← mul_div_assoc]
  gcongr
  linarith

/-- Both literal permanent bounds hold for every supplied controlled witness. -/
theorem same_root_recovery {m : ℕ} (hm : 0 < m) (Y : Matrix (Fin m) (Fin m) ℝ)
    (x y : Fin m → ℝ) {C ε q Cstar : ℝ}
    (hw : controlledWitness Y C ε q x y)
    (hC : 0 ≤ C) (hCs : C ≤ Cstar) (hq : q ≤ 85/92)
    (ht : ε ≤ RawScalingSynthesis.epsilonThreshold C q) :
    let M := expScaled Y x y
    let K := GeneralZerothTail.globalConstant (Real.exp (1/2)*Cstar) (177/184)
    |M.permanent/((m.factorial : ℝ)/(m : ℝ)^m) -
      (Real.sqrt ((1-(M-P m)ᵀ*(M-P m)).det))⁻¹| ≤ K/(m : ℝ) ∧
    |M.permanent-((m.factorial : ℝ)/(m : ℝ)^m)*
      (Real.sqrt ((1-(M-P m)ᵀ*(M-P m)).det))⁻¹| ≤
      ((m.factorial : ℝ)/(m : ℝ)^m)*(K/(m : ℝ)) := by
  dsimp only
  have hd := same_root_density hm Y x y hw hC hCs hq ht
  have hcaps := same_root_caps hm Y x y hw hC hCs hq ht
  have hroot := hw.2.2.1
  have hrow : ∀ i, ∑ j, expScaled Y x y i j = 1 := by
    simpa [expScaled] using hroot.1
  have hcol : ∀ j, ∑ i, expScaled Y x y i j = 1 := by
    simpa [expScaled] using hroot.2
  have hD : 0 ≤ Real.exp (1/2)*Cstar := mul_nonneg (Real.exp_pos _).le (hC.trans hCs)
  exact ⟨GeneralBalancedPermanent.actual_permanent_recovery hm _ _ _ hD
      (fun i j => (hd i j).1) (fun i j => (hd i j).2) hrow hcol
      (by norm_num) (by norm_num) hcaps.2.1,
    GeneralBalancedPermanent.actual_permanent_recovery_scaled hm _ _ _ hD
      (fun i j => (hd i j).1) (fun i j => (hd i j).2) hrow hcol
      (by norm_num) (by norm_num) hcaps.2.1⟩

/-- Uniform actual log-window endpoint. The exact supplied x,y and witness are retained. -/
theorem eventually_actual_recovery {A B a0 : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∀ᶠ n : ℕ in atTop, ∀ (T : Tournament n) (I J : Finset (Fin n))
      (m : ℕ) (e f : Fin m ↪ Fin n),
      (m : ℝ)=(n : ℝ)-(I.card : ℝ) →
      tau (normalizedScore T) ≤ A*Real.log (n : ℝ) →
      (I.card : ℝ) ≤ B*Real.log (n : ℝ) →
      let Y := actualDeleted T e f I J
      let C := density m (16*(scaleCap a0)^2) (actualK T a0 I)
      let ε := residualBudget n m I.card (16*(scaleCap a0)^2)
        (normalizedMarginalBound T a0) (actualK T a0 I)
      let q := gapBudget n m (39/46) (actualK T a0 I)
      ∀ (x y : Fin m → ℝ), controlledWitness Y C ε q x y →
      let M := expScaled Y x y
      (n : ℝ)/2 ≤ m ∧ controlledWitness Y C ε q x y ∧
      |M.permanent/((m.factorial : ℝ)/(m : ℝ)^m) -
        (Real.sqrt ((1-(M-P m)ᵀ*(M-P m)).det))⁻¹| ≤ fixedError a0/(m : ℝ) ∧
      |M.permanent-((m.factorial : ℝ)/(m : ℝ)^m)*
        (Real.sqrt ((1-(M-P m)ᵀ*(M-P m)).det))⁻¹| ≤
        ((m.factorial : ℝ)/(m : ℝ)^m)*(fixedError a0/(m : ℝ)) := by
  filter_upwards [eventually_gt_atTop 0,
    eventually_remaining_budgets (a0:=a0) hA hB,
    (totalRatio_tendsto A B a0).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 7/92))] with n hn hb hz
  intro T I J m e f hdim hτ ht
  dsimp only
  intro x y hw
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hbudget := hb T I m hdim hτ ht
  have hk0 : 0 ≤ actualK T a0 I := by
    have hδ := normalizedMarginalBound_nonneg T a0
    unfold actualK
    positivity
  have hratio : (I.card : ℝ)/(n : ℝ)+actualK T a0 I/(n : ℝ) ≤ 7/92 := by
    calc
      _ ≤ deletionRatio B n+kappaRatio A B a0 n := add_le_add
        (div_le_div_of_nonneg_right ht (Nat.cast_nonneg n))
        (actual_kappaRatio_le hn T I hA hB hτ ht)
      _ ≤ _ := hz.le
  have hsum : (I.card : ℝ)+actualK T a0 I ≤ (7/92)*(n : ℝ) := by
    apply (div_le_iff₀ hnR).mp
    simpa only [add_div] using hratio
  have hhalf : (n : ℝ)/2 ≤ m := by linarith
  have hm : 0 < m := by
    have hmR : (0 : ℝ) < m := by linarith
    exact_mod_cast hmR
  have hden : 0 < (m : ℝ)-actualK T a0 I := sub_pos.mpr hbudget.1
  have hC0 : 0 ≤ density m (16*(scaleCap a0)^2) (actualK T a0 I) := by
    unfold density
    positivity
  have he := deletion_envelopes hn hdim (by positivity)
    (show 0 ≤ 16*(scaleCap a0)^2 by positivity) hratio
  have hCstar : density m (16*(scaleCap a0)^2) (actualK T a0 I) ≤ 32*(scaleCap a0)^2 := by
    nlinarith [he.1]
  have hrec := same_root_recovery hm _ x y hw hC0 hCstar he.2 hbudget.2.2
  exact ⟨hhalf, hw, hrec⟩
end SameRootPermanentCandidate
