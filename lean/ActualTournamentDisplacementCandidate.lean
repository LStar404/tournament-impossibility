import FiniteCenteredDisplacementCandidate
import LogWindowFrobeniusUniformCandidate
import IndependentCenteringEnergyCandidate
/-! Actual tournament same-root displacement on a fixed
logarithmic window. No target displacement or squared root-error assumption. -/
set_option autoImplicit false
noncomputable section
namespace ActualTournamentDisplacementCandidate
open Matrix Finset Filter
open scoped Topology
open TournamentHamiltonian ActualTournamentPrescalingBounds ActualPrescalingNormalization
open TournamentPrescalingMassBound DeletedScalingSynthesisCandidate LogWindowDeletionBudgetCandidate
open SameRootFrobeniusCandidate LogWindowFrobeniusUniformCandidate
open IndependentCenteringEnergyCandidate ActualReconstructionBridgeCandidate
open ActualHessianFinite MatrixScalingMassPotential RealBilinearTrace RealGramEndpoint
open FiniteCenteredDisplacementCandidate
variable {n m : ℕ}

lemma actual_base_identity (T : Tournament n) :
    baseMatrix T=realZ T+constant n (1/((n:ℝ)-1)) := by
  ext i j
  simp only [baseMatrix, realZ, constant, Matrix.add_apply]
  ring

lemma actual_Z_fnorm (T : Tournament n) (hn : 2 ≤ n) : fnorm (realZ T) ≤ 2 := by
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hd : 0 < (n:ℝ)-1 := by linarith
  have he : frob (realZ T) ≤ (n:ℝ)^2/((n:ℝ)-1)^2 := by
    unfold frob
    calc
      _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, (1/((n:ℝ)-1))^2 := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        have hh := realZ_abs T hn i j
        nlinarith [sq_abs (realZ T i j), abs_nonneg (realZ T i j), div_nonneg (show (0:ℝ) ≤ 1 by norm_num) hd.le]
      _ = _ := by simp; ring
  have he4 : frob (realZ T) ≤ 4 := by
    apply he.trans
    apply (div_le_iff₀ (sq_pos_of_pos hd)).mpr
    nlinarith
  have hs := fnorm_sq (realZ T)
  have hf : 0 ≤ fnorm (realZ T) := norm_nonneg _
  nlinarith

lemma actual_deleted_marginals (T : Tournament n) (hn : 2 ≤ n)
    (e f : Fin m ↪ Fin n) (I J : Finset (Fin n))
    (he : univ.image e=Iᶜ) (hf : univ.image f=Jᶜ) (hcard : J.card=I.card)
    (hdim : (m:ℝ)=(n:ℝ)-(I.card:ℝ)) (hhalf : 2*I.card ≤ n)
    {a0 : ℝ} (h0 : 0 ≤ a0) (h1 : a0 < 1) (ha : ∀ i, |normalizedScore T i| ≤ a0)
    (hsmall : actualK T a0 I < (m:ℝ)) :
    (∀ i, |ActualHessianFinite.r (actualDeleted T e f I J) i| ≤
      residualBudget n m I.card (16*(scaleCap a0)^2) (normalizedMarginalBound T a0) (actualK T a0 I)) ∧
    (∀ j, |ActualHessianFinite.c (actualDeleted T e f I J) j| ≤
      residualBudget n m I.card (16*(scaleCap a0)^2) (normalizedMarginalBound T a0) (actualK T a0 I)) := by
  have hk := actual_independent_deletion_bound T hn h0 h1 ha I J hcard hhalf
  have hmarg := normalized_marginals T hn h0 h1 ha
  have hnon := normalized_nonneg T hn h0 h1 ha
  have hentry (i j : Fin n) : normalizedMatrix T i j ≤ (16*(scaleCap a0)^2)/(n:ℝ) :=
    (le_abs_self _).trans (normalized_entry_bound T hn h0 h1 ha i j)
  constructor
  · intro i
    simpa only [actualDeleted, actualK, ActualHessianFinite.r, ActualHessianFinite.row] using
      deleted_rows (show 0 < n by omega) (normalizedMatrix T) e f I J hf hcard hdim
        (by positivity) (normalizedMarginalBound_nonneg T a0) hk hsmall hnon hentry hmarg.1 i
  · intro j
    simpa only [actualDeleted, actualK, ActualHessianFinite.c, ActualHessianFinite.col] using
      deleted_cols (show 0 < n by omega) (normalizedMatrix T) e f I J he hdim
        (by positivity) (normalizedMarginalBound_nonneg T a0) hk hsmall hnon hentry hmarg.2 j

/-- Same supplied root, actual matrix objects, with all finite gates eventually
proved from fixed score/log windows. No root reselection or hsq premise. -/
theorem eventually_actual_same_root_displacement {A B a0 : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (h0 : 0 ≤ a0) (h1 : a0 < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ (T : Tournament n) (m : ℕ)
      (e f : Fin m ↪ Fin n) (I J : Finset (Fin n)),
      univ.image e=Iᶜ → univ.image f=Jᶜ → J.card=I.card →
      (m:ℝ)=(n:ℝ)-(I.card:ℝ) →
      (∀ i, |normalizedScore T i| ≤ a0) →
      tau (normalizedScore T) ≤ A*Real.log (n:ℝ) →
      (I.card:ℝ) ≤ B*Real.log (n:ℝ) →
      ∀ x y : Fin m → ℝ,
      controlledWitness (actualDeleted T e f I J)
        (density m (16*(scaleCap a0)^2) (actualK T a0 I))
        (residualBudget n m I.card (16*(scaleCap a0)^2) (normalizedMarginalBound T a0) (actualK T a0 I))
        (gapBudget n m (39/46) (actualK T a0 I)) x y →
      fnorm (expScaled (actualDeleted T e f I J) x y-P m-center ((realZ T).submatrix e f)) ≤
        Real.sqrt (fixedCoefficient a0)*
          residualBudget n m I.card (16*(scaleCap a0)^2) (normalizedMarginalBound T a0) (actualK T a0 I)+
        2*fnorm (normalizedMatrix T-baseMatrix T)+4*((I.card:ℝ)+actualK T a0 I)/(n:ℝ) := by
  filter_upwards [eventually_ge_atTop 2, eventually_actual_coefficient (a0:=a0) hA hB,
    (totalRatio_tendsto A B a0).eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/4))]
    with n hn hcoef hratio
  intro T m e f I J he hf hcard hdim ha htau ht x y hw
  have hn0 : 0 < n := by omega
  have hnR : (0:ℝ) < n := by exact_mod_cast hn0
  have hk0 : 0 ≤ actualK T a0 I := by
    have hd0 := normalizedMarginalBound_nonneg T a0
    unfold actualK
    positivity
  have hr : (I.card:ℝ)/(n:ℝ)+actualK T a0 I/(n:ℝ) ≤ 1/4 := by
    calc
      _ ≤ deletionRatio B n+kappaRatio A B a0 n := add_le_add
        (div_le_div_of_nonneg_right ht hnR.le) (actual_kappaRatio_le hn0 T I hA hB htau ht)
      _ ≤ _ := hratio.le
  have hs : (I.card:ℝ)+actualK T a0 I ≤ (n:ℝ)/4 := by
    have hh := (div_le_iff₀ hnR).mp (show ((I.card:ℝ)+actualK T a0 I)/(n:ℝ) ≤ 1/4 by simpa only [add_div] using hr)
    linarith
  have hgap : (n:ℝ)/2 ≤ (m:ℝ)-actualK T a0 I := by linarith
  have hsmall : actualK T a0 I < (m:ℝ) := by linarith
  have hm0 : 0 < m := by exact_mod_cast (lt_of_le_of_lt hk0 hsmall)
  have hhalf : 2*I.card ≤ n := by
    have hh : (2:ℝ)*(I.card:ℝ) ≤ (n:ℝ) := by linarith
    exact_mod_cast hh
  have hk := actual_independent_deletion_bound T hn h0 h1 ha I J hcard hhalf
  have hmarg := actual_deleted_marginals T hn e f I J he hf hcard hdim hhalf h0 h1 ha hsmall
  have hCpos : 0 ≤ density m (16*(scaleCap a0)^2) (actualK T a0 I) := by
    unfold density
    have hd := sub_pos.mpr hsmall
    positivity
  have heps : 0 ≤ residualBudget n m I.card (16*(scaleCap a0)^2)
      (normalizedMarginalBound T a0) (actualK T a0 I) := by
    unfold residualBudget
    have hd := sub_pos.mpr hsmall
    have hdelta := normalizedMarginalBound_nonneg T a0
    positivity
  have hKs : 0 ≤ fixedCoefficient a0 := by unfold fixedCoefficient; positivity
  have hsq := same_root_squared_bound hm0 (actualDeleted T e f I J) x y hCpos heps hw hmarg.1 hmarg.2
  have hsq' : SameRootFrobeniusCandidate.sqF (expScaled (actualDeleted T e f I J) x y-actualDeleted T e f I J) ≤
      fixedCoefficient a0*(residualBudget n m I.card (16*(scaleCap a0)^2)
        (normalizedMarginalBound T a0) (actualK T a0 I))^2 :=
    hsq.trans (mul_le_mul_of_nonneg_right (hcoef T I m hdim htau ht) (sq_nonneg _))
  have hh := normalized_same_root_displacement hm0 hnR (normalizedMatrix T) (baseMatrix T) (realZ T)
    e f (1/((n:ℝ)-1)) (I.card:ℝ)
    (IndependentDeletionMass.deletionExcess (normalizedMatrix T) I J) (actualK T a0 I)
    (by positivity) hdim hk hgap (actual_base_identity T) (actual_Z_fnorm T hn)
    x y _ _ _ (fixedCoefficient a0) hw hKs heps hsq'
  exact hh
end ActualTournamentDisplacementCandidate
