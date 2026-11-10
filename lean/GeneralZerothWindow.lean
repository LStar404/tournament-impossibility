import GeneralBalancedWeighted
import PermanentTruncatedRecoveryAlgebra
import ActivityFiniteWindowBound

/-! Genuine p=0 finite coefficient window from raw matrix hypotheses. -/
set_option autoImplicit false
noncomputable section
namespace GeneralZerothWindow
open Matrix WeightedCoefficientNorm BalancedRawData GeneralBalancedWeighted
open ActualResidualFrozenFactorization BinaryGraphActivityBound
open FiniteFactorialRecovery PermanentNormalizedFrozenBridge PermanentTruncatedRecoveryAlgebra

def recoveryRadius (q : ℝ) : ℝ := 1+(1-q)/8
def coreMajorant (C q : ℝ) : ℝ := coreConstant C (innerRadius q) (outerRadius q) q
def activityMajorant (C q : ℝ) : ℝ := activityConstant C (innerRadius q) (outerRadius q) q
def cutoff (C q : ℝ) : ℝ := min (1/2) (min (Real.log (recoveryRadius q))
  (1/(4*Real.exp 1*activityMajorant C q)))
def degree (C q : ℝ) (n : ℕ) : ℕ := ⌊cutoff C q*(n : ℝ)⌋₊
def window (C q : ℝ) (n : ℕ) : Finset ℕ := Finset.range (degree C q n+1)
def errorConstant (C q : ℝ) : ℝ := coreMajorant C q*
  (WeightedPolynomialMultiplier.moment (recoveryRadius q/innerRadius q) 2+2*activityMajorant C q)

lemma recovery_radius_data {q : ℝ} (hq : q < 1) :
    1 < recoveryRadius q ∧ recoveryRadius q < innerRadius q := by
  unfold recoveryRadius innerRadius
  constructor <;> linarith

lemma activity_majorant_pos (C q : ℝ) : 0 < activityMajorant C q :=
  activity_pos C (innerRadius q) (outerRadius q) q

lemma cutoff_pos (C : ℝ) {q : ℝ} (hq : q < 1) : 0 < cutoff C q := by
  have hD := activity_majorant_pos C q
  exact lt_min (by norm_num) (lt_min (Real.log_pos (recovery_radius_data hq).1) (by positivity))

lemma cutoff_activity_budget (C q : ℝ) :
    cutoff C q ≤ 1/(4*Real.exp 1*activityMajorant C q) :=
  (min_le_right _ _).trans (min_le_right _ _)

/-- No degree positivity assumption: degree zero is included. -/
lemma budget (C : ℝ) {q : ℝ} (hq : q < 1) (n k : ℕ) (hn : 0 < n)
    (hk : k ∈ window C q n) :
    2*k ≤ n ∧ (k : ℝ)/(n : ℝ) ≤ Real.log (recoveryRadius q) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hkN : k ≤ degree C q n := by simpa [window] using hk
  have hkR : (k : ℝ) ≤ cutoff C q*(n : ℝ) :=
    (by exact_mod_cast hkN : (k : ℝ) ≤ (degree C q n : ℝ)).trans
      (Nat.floor_le (mul_nonneg (cutoff_pos C hq).le (Nat.cast_nonneg n)))
  have hhalf : cutoff C q ≤ (1/2 : ℝ) := min_le_left _ _
  have hlog : cutoff C q ≤ Real.log (recoveryRadius q) :=
    (min_le_right _ _).trans (min_le_left _ _)
  constructor
  · have hb := mul_le_mul_of_nonneg_right hhalf hnR.le
    have hh : (2 : ℝ)*(k : ℝ) ≤ (n : ℝ) := by nlinarith
    exact_mod_cast hh
  · apply (div_le_iff₀ hnR).mpr
    exact hkR.trans (mul_le_mul_of_nonneg_right hlog hnR.le)

lemma degree_le (C : ℝ) {q : ℝ} (hq : q < 1) (n : ℕ) (hn : 0 < n) :
    degree C q n ≤ n := by
  have h := budget C hq n (degree C q n) hn (by simp [window])
  omega

lemma recovered_window (n : ℕ) (hn : 0 < n) (F : PowerSeries ℂ) (E : Finset ℕ)
    (sigma rho : ℝ) (hsigma : 1 < sigma) (hsr : sigma ≤ rho) (hF : Finite rho F)
    (hE : ∀ k ∈ E, 2*k ≤ n ∧ (k : ℝ)/(n : ℝ) ≤ Real.log sigma) :
    (∑ k ∈ E, factorialRecoveryRatio n k*‖F.coeff k‖) ≤ norm rho F := by
  have hsigma0 : 0 ≤ sigma := (zero_lt_one.trans hsigma).le
  have hrho : 0 ≤ rho := hsigma0.trans hsr
  calc
    _ ≤ ∑ k ∈ E, mass rho F k := by
      apply Finset.sum_le_sum
      intro k hk
      have hr := factorialRecoveryRatio_le_pow n k hn (hE k hk).1 sigma hsigma (hE k hk).2
      have hp := pow_le_pow_left₀ hsigma0 hsr k
      simpa only [mass, mul_comm] using
        mul_le_mul_of_nonneg_right (hr.trans hp) (norm_nonneg (F.coeff k))
    _ ≤ _ := hF.sum_le_tsum E (fun k _ => nonneg hrho F k)

lemma recovered_coefficient_zero {n : ℕ} (N : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    recoveredCoefficient N 0 k=(core N).coeff k := by
  simp [recoveredCoefficient, multiplier, RecoveryFiniteOrderRemainder.H,
    RecoveryHomogeneousList.zero, CoreActivityFiniteProjection.zero_activity_product]

section Actual
variable {n : ℕ} (hn : 0 < n) (M : Matrix (Fin n) (Fin n) ℝ)
variable (C q : ℝ) (hC : 0 ≤ C)
variable (hM : ∀ i j, 0 ≤ M i j) (hd : ∀ i j, M i j ≤ C/(n : ℝ))
variable (hr : ∀ i, (∑ j, M i j)=1) (hc : ∀ j, (∑ i, M i j)=1)
variable (hq0 : 0 ≤ q) (hq1 : q < 1)
variable (hN : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (M-ActualHessianFinite.P n)‖ ≤ q)
include hn hC hM hd hr hc hq0 hq1 hN

lemma core_multiplier_error :
    ActivityFactorialMultiplier.error n 0 (core (centeredComplex M)) (window C q n) 1 ≤
      (WeightedPolynomialMultiplier.moment (recoveryRadius q/innerRadius q) 2*
        coreMajorant C q)/(n : ℝ) := by
  have hu := actual_uniform_bounds hn M C q hC hM hd hr hc hq0 hq1 hN
  have hs := recovery_radius_data hq1
  have h := CoreActivityFactorialBridge.zeroth_order_bound n 0 hn
    (core (centeredComplex M)) (window C q n) 1 (innerRadius q) (recoveryRadius q)
    (coreMajorant C q) (by norm_num) (zero_lt_one.trans hu.1) hs.1
    (by simpa only [mul_one] using hs.2) hu.2.1.1 hu.2.1.2
    (fun k hk => budget C hq1 n k hn hk)
  simpa only [mul_one, Nat.zero_add, Nat.mul_one, pow_one] using h

lemma high_activity_mass :
    (∑ j ∈ Finset.Ico 1 (degree C q n+1), ∑ k ∈ window C q n,
      factorialRecoveryRatio n k*‖(core (centeredComplex M)*rawActivity (centeredComplex M) j).coeff k‖)
      ≤2*coreMajorant C q*activityMajorant C q/(n : ℝ) := by
  have hu := actual_uniform_bounds hn M C q hC hM hd hr hc hq0 hq1 hN
  have hs := recovery_radius_data hq1
  have hB : 0 ≤ coreMajorant C q := (Real.exp_pos _).le
  have h := ActivityFiniteWindowBound.dominated_floor_window
    (activity_majorant_pos C q) (cutoff_pos C hq1).le (cutoff_activity_budget C q) hB n 0 hn
    (fun j => ∑ k ∈ window C q n,
      factorialRecoveryRatio n k*‖(core (centeredComplex M)*rawActivity (centeredComplex M) j).coeff k‖) ?_
  · convert h using 1 <;> simp only [degree, Nat.zero_add, Nat.cast_zero, zero_add, mul_one, pow_one]
    <;> ring
  · intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
    have hp := hu.2.2 j hj1
    have hw := recovered_window n hn _ (window C q n) (recoveryRadius q) (innerRadius q)
      hs.1 hs.2.le hp.1 (fun k hk => budget C hq1 n k hn hk)
    simpa only [ActivityFiniteWindowBound.term, coreMajorant, activityMajorant] using hw.trans hp.2

/-- The finite coefficient estimate is derived from actual M, not assumed. -/
theorem actual_window_error :
    (∑ k ∈ window C q n,
      ‖(normalized (centeredComplex M)).coeff k-(core (centeredComplex M)).coeff k‖)
      ≤errorConstant C q/(n : ℝ) := by
  let N := centeredComplex M
  have hw := finite_window_error N hn 0 (degree C q n) (Nat.zero_le _) (degree_le C hq1 n hn)
  have hlo := core_multiplier_error hn M C q hC hM hd hr hc hq0 hq1 hN
  have hhi := high_activity_mass hn M C q hC hM hd hr hc hq0 hq1 hN
  have hlowsum :
      (∑ j ∈ Finset.range (0+1), ActivityFactorialMultiplier.error n (0-j)
        (core N*rawActivity N j) (window C q n) 1) ≤
      (WeightedPolynomialMultiplier.moment (recoveryRadius q/innerRadius q) 2*
        coreMajorant C q)/(n : ℝ) := by
    simpa only [Nat.zero_add, Finset.sum_range_one, Nat.sub_zero,
      CoreActivityFiniteProjection.zero_activity_product] using hlo
  have heq : (∑ k ∈ window C q n, ‖(normalized N).coeff k-(core N).coeff k‖)=
      ∑ k ∈ Finset.range (degree C q n+1),
        ‖(normalized N).coeff k-(approximation N 0 (degree C q n)).coeff k‖ := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ degree C q n := by simpa [window] using hk
    rw [coefficient N 0 (degree C q n) k hk', recovered_coefficient_zero]
  change (∑ k ∈ window C q n, ‖(normalized N).coeff k-(core N).coeff k‖) ≤ _
  rw [heq]
  calc
    _ ≤ _ := hw
    _ ≤ (WeightedPolynomialMultiplier.moment (recoveryRadius q/innerRadius q) 2*
        coreMajorant C q)/(n : ℝ) + 2*coreMajorant C q*activityMajorant C q/(n : ℝ) :=
      add_le_add hlowsum hhi
    _ = _ := by unfold errorConstant; ring
end Actual
end GeneralZerothWindow
#check @GeneralZerothWindow.actual_window_error
#print axioms GeneralZerothWindow.actual_window_error
