import SameRootFrobeniusCandidate
import LogWindowDeletionBudgetCandidate
set_option autoImplicit false
noncomputable section
namespace LogWindowFrobeniusUniformCandidate
open SameRootFrobeniusCandidate

/-- Threshold itself supplies epsilon<=1 and radius<=1/4. -/
lemma threshold_radius {C ε q : ℝ} (hC : 0 ≤ C) (hq : q < 1)
    (hε : ε ≤ RawScalingSynthesis.epsilonThreshold C q) :
    ε ≤ 1 ∧ RawScalingSynthesis.radius C q ε ≤ 1/4 ∧
      (1-q)/2 ≤ 1-q-4*ε := by
  have hk : 0 < RawMatrixScalingExistence.rawK C q := by
    unfold RawMatrixScalingExistence.rawK
    exact mul_pos (by norm_num) (ScalingEpsilonThreshold.inverse_constant_pos hC hq)
  have hraw : ε ≤ ScalingEpsilonThreshold.threshold (RawMatrixScalingExistence.rawK C q) :=
    hε.trans (min_le_left _ _)
  have he1 : ε ≤ 1 := hraw.trans (min_le_left _ _)
  have he8 : ε ≤ 1/(8*RawMatrixScalingExistence.rawK C q) :=
    hraw.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hegap : ε ≤ (1-q)/8 := hε.trans (min_le_right _ _)
  refine ⟨he1, ?_, by linarith⟩
  unfold RawScalingSynthesis.radius
  have hh := (le_div_iff₀ (show 0 < 8*RawMatrixScalingExistence.rawK C q by positivity)).mp he8
  nlinarith

/-- All four coefficient inputs collapse to the fixed density envelope and
q<=85/92; the existing scaling threshold supplies the other bounds. -/
lemma uniform_coefficient {C ε q Cstar : ℝ}
    (hC : 0 ≤ C) (hε : 0 ≤ ε) (hCs : C ≤ Cstar)
    (hq : q ≤ 85/92) (ht : ε ≤ RawScalingSynthesis.epsilonThreshold C q) :
    coefficient C ε q ≤
      4*Cstar*(1+1)*Real.exp (4*(1/4:ℝ))*(Real.exp (2*(1/4:ℝ))/(7/184))^2 := by
  have hh := threshold_radius hC (show q < 1 by linarith) ht
  exact coefficient_uniform hC hε (by norm_num) hCs hh.1 hh.2.1 (by linarith [hh.2.2])

lemma deletion_envelopes {n m : ℕ} {t C K : ℝ}
    (hn : 0 < n) (hm : (m:ℝ)=(n:ℝ)-t) (ht : 0 ≤ t) (hC : 0 ≤ C)
    (hz : t/(n:ℝ)+K/(n:ℝ) ≤ 7/92) :
    DeletedScalingSynthesisCandidate.density m C K ≤ 2*C ∧
    DeletedScalingSynthesisCandidate.gapBudget n m (39/46) K ≤ 85/92 := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hs : t+K ≤ (7/92)*(n:ℝ) := by
    apply (div_le_iff₀ hnR).mp
    simpa only [add_div] using hz
  have hd : (n:ℝ)/2 ≤ (m:ℝ)-K := by linarith
  have hd0 : 0 < (m:ℝ)-K := by linarith
  constructor
  · unfold DeletedScalingSynthesisCandidate.density
    apply (div_le_iff₀ hd0).mpr
    have h1 := mul_le_mul_of_nonneg_left hd hC
    have h2 := mul_le_mul_of_nonneg_left (show (m:ℝ) ≤ n by linarith) hC
    nlinarith
  · unfold DeletedScalingSynthesisCandidate.gapBudget
    apply (div_le_iff₀ hd0).mpr
    nlinarith

open Filter
open scoped Topology
open TournamentHamiltonian ActualTournamentPrescalingBounds ActualPrescalingNormalization
open DeletedScalingSynthesisCandidate LogWindowDeletionBudgetCandidate TournamentPrescalingMassBound

def fixedCoefficient (a0 : ℝ) : ℝ :=
  4*(32*(scaleCap a0)^2)*(1+1)*Real.exp (4*(1/4:ℝ))*
    (Real.exp (2*(1/4:ℝ))/(7/184))^2

/-- One eventual cutoff is uniform over all actual tournaments and deletions
in a fixed log window. No extra radius/epsilon/denominator inputs. -/
theorem eventually_actual_coefficient {A B a0 : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∀ᶠ n : ℕ in atTop, ∀ (T : Tournament n) (I : Finset (Fin n)) (m : ℕ),
      (m:ℝ)=(n:ℝ)-(I.card:ℝ) →
      tau (normalizedScore T) ≤ A*Real.log (n:ℝ) →
      (I.card:ℝ) ≤ B*Real.log (n:ℝ) →
      coefficient (density m (16*(scaleCap a0)^2) (actualK T a0 I))
        (residualBudget n m I.card (16*(scaleCap a0)^2)
          (normalizedMarginalBound T a0) (actualK T a0 I))
        (gapBudget n m (39/46) (actualK T a0 I)) ≤ fixedCoefficient a0 := by
  filter_upwards [eventually_gt_atTop 0,
    eventually_remaining_budgets (a0:=a0) hA hB,
    (totalRatio_tendsto A B a0).eventually
      (gt_mem_nhds (by norm_num : (0:ℝ)<7/92))] with n hn hb hz
  intro T I m hm hτ ht
  have hbudget := hb T I m hm hτ ht
  have hd0 := normalizedMarginalBound_nonneg T a0
  have hk0 : 0 ≤ actualK T a0 I := by unfold actualK; positivity
  have hden : 0 < (m:ℝ)-actualK T a0 I := sub_pos.mpr hbudget.1
  have hC0 : 0 ≤ density m (16*(scaleCap a0)^2) (actualK T a0 I) := by
    unfold density; positivity
  have hε0 : 0 ≤ residualBudget n m I.card (16*(scaleCap a0)^2)
      (normalizedMarginalBound T a0) (actualK T a0 I) := by
    unfold residualBudget; positivity
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
  exact uniform_coefficient hC0 hε0 hCstar he.2 hbudget.2.2

end LogWindowFrobeniusUniformCandidate
