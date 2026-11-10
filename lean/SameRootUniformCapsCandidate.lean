import LogWindowFrobeniusUniformCandidate
set_option autoImplicit false
noncomputable section
namespace SameRootUniformCapsCandidate
open Matrix Finset ActualHessianFinite ActualHessianComplex MatrixScalingMassPotential
open ActualReconstructionBridgeCandidate SameRootFrobeniusCandidate
open LogWindowFrobeniusUniformCandidate
variable {m : ℕ}

lemma density_mass_sqF (hm : 0 < m) (M : Matrix (Fin m) (Fin m) ℝ) {D : ℝ}
    (hentry : ∀ i j, 0 ≤ M i j ∧ M i j ≤ D/(m:ℝ))
    (hrow : ∀ i, ∑ j, M i j = 1) : sqF M ≤ D := by
  have hmR : (m:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  calc
    sqF M ≤ ∑ i, ∑ j, (D/(m:ℝ))*M i j := by
      apply sum_le_sum; intro i _
      apply sum_le_sum; intro j _
      nlinarith [mul_le_mul_of_nonneg_right (hentry i j).2 (hentry i j).1]
    _ = D := by simp_rw [← Finset.mul_sum, hrow]; simp [hmR]

/-- Supplied witness unchanged: balanced potential and Gamma can be retained. -/
theorem same_root_caps (hm : 0 < m) (Y : Matrix (Fin m) (Fin m) ℝ)
    (x y : Fin m → ℝ) {C ε q Cstar : ℝ}
    (hw : controlledWitness Y C ε q x y)
    (hC : 0 ≤ C) (hCs : C ≤ Cstar) (hq : q ≤ 85/92)
    (ht : ε ≤ RawScalingSynthesis.epsilonThreshold C q) :
    controlledWitness Y C ε q x y ∧
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (expScaled Y x y-P m)‖ ≤ 177/184 ∧
    sqF (expScaled Y x y) ≤ Real.exp (1/2)*Cstar ∧
    sqF (expScaled Y x y-P m) ≤ Real.exp (1/2)*Cstar := by
  have hradius := (threshold_radius hC (show q < 1 by linarith) ht).2.1
  have hroot := hw.2.2.1
  have hrow : ∀ i, ∑ j, expScaled Y x y i j = 1 := by
    simpa [expScaled] using hroot.1
  have hcol : ∀ j, ∑ i, expScaled Y x y i j = 1 := by
    simpa [expScaled] using hroot.2
  have hcstar : 0 ≤ Cstar := hC.trans hCs
  have hd : ∀ i j, 0 ≤ expScaled Y x y i j ∧
      expScaled Y x y i j ≤ (Real.exp (1/2)*Cstar)/(m:ℝ) := by
    intro i j
    refine ⟨(hw.2.2.2.2.1 i j).1, (hw.2.2.2.2.1 i j).2.trans ?_⟩
    rw [← mul_div_assoc]
    gcongr
    linarith
  have hF := density_mass_sqF hm (expScaled Y x y) hd hrow
  have hgap : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (realComplex (expScaled Y x y-P m))‖ ≤ 177/184 := by
    exact hw.2.2.2.2.2.2.2.1.trans (by linarith)
  refine ⟨hw, RawScalingSynthesis.real_gap_of_complex _ (by norm_num) hgap, hF, ?_⟩
  rw [ScalingCenteredGap.doubly_stochastic_centering hm _ hrow hcol]
  exact (centered_sqF_contraction hm _).trans hF

open Filter
open scoped Topology
open TournamentHamiltonian ActualTournamentPrescalingBounds ActualPrescalingNormalization
open DeletedScalingSynthesisCandidate LogWindowDeletionBudgetCandidate TournamentPrescalingMassBound

/-- Uniform actual endpoint, for every supplied controlled witness of the
same actualDeleted matrix. No existence theorem is called again. -/
theorem eventually_actual_caps {A B a0 : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∀ᶠ n : ℕ in atTop, ∀ (T : Tournament n) (I J : Finset (Fin n))
      (m : ℕ) (e f : Fin m ↪ Fin n), 0 < m →
      (m:ℝ)=(n:ℝ)-(I.card:ℝ) →
      tau (normalizedScore T) ≤ A*Real.log (n:ℝ) →
      (I.card:ℝ) ≤ B*Real.log (n:ℝ) →
      let Y := actualDeleted T e f I J
      let C := density m (16*(scaleCap a0)^2) (actualK T a0 I)
      let ε := residualBudget n m I.card (16*(scaleCap a0)^2)
        (normalizedMarginalBound T a0) (actualK T a0 I)
      let q := gapBudget n m (39/46) (actualK T a0 I)
      ∀ (x y : Fin m → ℝ), controlledWitness Y C ε q x y →
        controlledWitness Y C ε q x y ∧
        ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (expScaled Y x y-P m)‖ ≤ 177/184 ∧
        sqF (expScaled Y x y) ≤ Real.exp (1/2)*(32*(scaleCap a0)^2) ∧
        sqF (expScaled Y x y-P m) ≤ Real.exp (1/2)*(32*(scaleCap a0)^2) := by
  filter_upwards [eventually_gt_atTop 0,
    eventually_remaining_budgets (a0:=a0) hA hB,
    (totalRatio_tendsto A B a0).eventually
      (gt_mem_nhds (by norm_num : (0:ℝ)<7/92))] with n hn hb hz
  intro T I J m e f hm0 hm hτ ht
  dsimp only
  intro x y hw
  have hbudget := hb T I m hm hτ ht
  have hden : 0 < (m:ℝ)-actualK T a0 I := sub_pos.mpr hbudget.1
  have hC0 : 0 ≤ density m (16*(scaleCap a0)^2) (actualK T a0 I) := by
    unfold density; positivity
  have hratio : (I.card:ℝ)/(n:ℝ)+actualK T a0 I/(n:ℝ) ≤ 7/92 := by
    calc
      _ ≤ deletionRatio B n+kappaRatio A B a0 n := add_le_add
        (div_le_div_of_nonneg_right ht (Nat.cast_nonneg n))
        (actual_kappaRatio_le hn T I hA hB hτ ht)
      _ ≤ _ := hz.le
  have he := deletion_envelopes hn hm (by positivity)
    (show 0 ≤ 16*(scaleCap a0)^2 by positivity) hratio
  have hCstar : density m (16*(scaleCap a0)^2) (actualK T a0 I) ≤ 32*(scaleCap a0)^2 := by
    nlinarith [he.1]
  exact same_root_caps hm0 _ x y hw hC0 hCstar he.2 hbudget.2.2

end SameRootUniformCapsCandidate
