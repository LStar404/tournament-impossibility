import WeightedRecoveryClosure
import ActualTruncatedPermanentRecovery

/-! Actual fixed-depth recovery
with all fixed k^ell weights, removal of the approximant cutoff, and the
falling-factorial coefficient interface at z=1. Analytic iteratedDeriv
identification is deliberately not asserted. -/
noncomputable section
namespace ActualWeightedUntruncatedRecovery
open WeightedCoefficientNorm ActualGraphCoreRecovery ActualResidualFrozenFactorization
open BinaryGraphActivityBound PermanentNormalizedFrozenBridge
open RecoveryMomentTail WeightedRecoveryClosure FiniteFactorialRecovery

def activityNumerator (d j : ℕ) : ℝ :=
  ActualCoreWeightedBound.coreConstant d*(activityConstant d*(j : ℝ))^j

def lowConstant (d p ell : ℕ) : ℝ := ∑ j∈Finset.range (p+1),
  WeightedPolynomialMultiplier.moment (17/18) (2*(p-j+1)+ell)*activityNumerator d j

def highConstant (d p ell : ℕ) : ℝ :=
  WeightedPolynomialMultiplier.moment (17/18) ell*ActualGraphCoreRecovery.highConstant d p

def actualTailConstant (d p ell : ℕ) : ℝ := ActualTruncatedPermanentRecovery.tailConstant d (p+ell)
def approximationTailConstant (d p ell : ℕ) : ℝ :=
  RecoveryMomentTail.tailConstant (cutoff d) (activityNumerator d) p ell

def errorConstant (d p ell : ℕ) : ℝ :=
  lowConstant d p ell+highConstant d p ell+actualTailConstant d p ell+approximationTailConstant d p ell

section Graph
variable {C : Type*} [Fintype C] [DecidableEq C] {n : ℕ}
variable (hn : 24≤n) (d : ℕ)
variable (e : BinaryBalancedTensor.Bits (d+1) ≃ Fin (2^(d+1))) (B : Matrix C C ℝ)
variable (hB : ∀ i j, B j i= -B i j) (he : ∀ i j, |B i j|≤1)
variable (f : Fin n ≃ C × BinaryBalancedTensor.Bits (d+1)) (v : ℝ) (hv : |v|≤1)
include hn hB he hv

lemma product_bound_all (j : ℕ) :
    let M := TournamentSkewMargin.branch (BinaryRawGraphWeighted.realGraph (d+1) e B f) v
    Finite (9/8) (core M*rawActivity M j) ∧
      norm (9/8) (core M*rawActivity M j)≤activityNumerator d j/(n : ℝ)^j := by
  by_cases hj : j=0
  · subst j
    dsimp only
    rw [CoreActivityFiniteProjection.zero_activity_product]
    simpa only [activityNumerator, pow_zero, mul_one, div_one] using
      ActualCoreWeightedBound.graph hn d e B hB he f v hv
  · have h := ActualGraphCoreRecovery.product_bound hn d e B hB he f v hv j (by omega)
    dsimp only at h ⊢
    refine ⟨h.1, ?_⟩
    apply h.2.trans_eq
    simp only [activityNumerator, div_pow]
    ring

lemma low_sum (p ell : ℕ) :
    let M := TournamentSkewMargin.branch (BinaryRawGraphWeighted.realGraph (d+1) e B f) v
    (∑ j∈Finset.range (p+1), WeightedRecoveryMultiplier.error n (p-j) ell
      (core M*rawActivity M j) (window d n))≤lowConstant d p ell/(n : ℝ)^(p+1) := by
  dsimp only
  calc
    _ ≤ ∑ j∈Finset.range (p+1),
        WeightedPolynomialMultiplier.moment (17/18) (2*(p-j+1)+ell)*activityNumerator d j/(n : ℝ)^(p+1) := by
      apply Finset.sum_le_sum
      intro j hj
      have h := product_bound_all hn d e B hB he f v hv j
      dsimp only at h
      exact WeightedRecoveryMultiplier.order_bound n p j ell (by omega) (by simpa using hj)
        _ (window d n) _ h.1 h.2 (fun k hk => budget d n k (by omega) hk)
    _ = _ := by rw [← Finset.sum_div]; rfl

lemma high_sum (p ell : ℕ) :
    let M := TournamentSkewMargin.branch (BinaryRawGraphWeighted.realGraph (d+1) e B f) v
    (∑ j∈Finset.Ico (p+1) (degree d n+1), ∑ k∈window d n,
      factorialRecoveryRatio n k*(k : ℝ)^ell*‖(core M*rawActivity M j).coeff k‖)≤
        highConstant d p ell/(n : ℝ)^(p+1) := by
  dsimp only
  have hm : 0≤WeightedPolynomialMultiplier.moment (17/18) ell := tsum_nonneg (fun k => by positivity)
  have hh := ActivityFiniteWindowBound.dominated_floor_window (activityConstant_pos d)
    (cutoff_pos d).le (min_le_right _ _) (mul_nonneg hm (coreConstant_nonneg d)) n p (by omega)
    (fun j => ∑ k∈window d n, factorialRecoveryRatio n k*(k : ℝ)^ell*‖(core
      (TournamentSkewMargin.branch (BinaryRawGraphWeighted.realGraph (d+1) e B f) v)*
      rawActivity (TournamentSkewMargin.branch (BinaryRawGraphWeighted.realGraph (d+1) e B f) v) j).coeff k‖) ?_
  · convert hh using 1 <;> simp only [degree, highConstant, ActualGraphCoreRecovery.highConstant] <;> ring
  · intro j hj
    have hj1 : 1≤j := by simp only [Finset.mem_Ico] at hj; omega
    have hb := ActualGraphCoreRecovery.product_bound hn d e B hB he f v hv j hj1
    dsimp only at hb
    have hw := WeightedRecoveryMultiplier.recovered_window n ell (by omega) _ (window d n) hb.1
      (fun k hk => budget d n k (by omega) hk)
    apply hw.trans
    convert mul_le_mul_of_nonneg_left hb.2 hm using 1 <;>
      simp only [ActivityFiniteWindowBound.term] <;> ring

/-- Uses the actual polynomial's higher-order unweighted tail and degree≤n.
No new circle estimate and no proxy coefficients are introduced. -/
lemma polynomial_tail (p ell : ℕ) :
    let M := TournamentSkewMargin.branch (BinaryRawGraphWeighted.realGraph (d+1) e B f) v
    (∑ k∈(normalized M).support.filter (fun k => degree d n<k),
      weight ell k*‖(normalized M).coeff k‖)≤actualTailConstant d p ell/(n : ℝ)^(p+1) := by
  let M := TournamentSkewMargin.branch (BinaryRawGraphWeighted.realGraph (d+1) e B f) v
  have hnR : (0 : ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have ht := PermanentNormalizedTailBridge.graph_tail hn d e B hB he f v hv (cutoff_pos d) (p+ell+1)
  dsimp only at ht ⊢
  change (∑ k∈(normalized M).support.filter (fun k => degree d n<k),
    weight ell k*‖(normalized M).coeff k‖)≤actualTailConstant d p ell/(n : ℝ)^(p+1)
  calc
    _ ≤ (n : ℝ)^ell*(∑ k∈(normalized M).support.filter (fun k => degree d n<k),
        ‖(normalized M).coeff k‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro k hk
      have hk0 := Polynomial.mem_support_iff.mp (Finset.mem_filter.mp hk).1
      have hkn : k≤n := by
        by_contra h
        exact hk0 (coefficient_zero_above M k (by omega))
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact pow_le_pow_left₀ (Nat.cast_nonneg k) (by exact_mod_cast hkn) ell
    _ ≤ (n : ℝ)^ell*(actualTailConstant d p ell/(n : ℝ)^(p+ell+1)) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ = _ := by
      rw [show p+ell+1=ell+(p+1) by omega, pow_add]
      field_simp

lemma approximation_tail (p ell : ℕ) (E : Finset ℕ) (hE : ∀ k∈E, degree d n<k) :
    let M := TournamentSkewMargin.branch (BinaryRawGraphWeighted.realGraph (d+1) e B f) v
    (∑ k∈E, weight ell k*‖(untruncated M p).coeff k‖)≤
      approximationTailConstant d p ell/(n : ℝ)^(p+1) := by
  apply RecoveryMomentTail.approximation_tail _ (by omega) p ell (cutoff d) (cutoff_pos d)
    (activityNumerator d)
  · intro j hj
    exact (product_bound_all hn d e B hB he f v hv j).1
  · intro j hj
    exact (product_bound_all hn d e B hB he f v hv j).2
  · exact hE

lemma window_error (p ell : ℕ) (hp : p≤degree d n) :
    let M := TournamentSkewMargin.branch (BinaryRawGraphWeighted.realGraph (d+1) e B f) v
    (∑ k∈Finset.range (degree d n+1), coefficientError (normalized M) (untruncated M p) ell k)≤
      (lowConstant d p ell+highConstant d p ell)/(n : ℝ)^(p+1) := by
  let M := TournamentSkewMargin.branch (BinaryRawGraphWeighted.realGraph (d+1) e B f) v
  have hw := WeightedRecoveryMultiplier.window_error M (by omega) p (degree d n) ell hp
    (ActualTruncatedPermanentRecovery.degree_le d n (by omega))
  have hL := low_sum hn d e B hB he f v hv p ell
  have hH := high_sum hn d e B hB he f v hv p ell
  dsimp only at hL hH ⊢
  have hh := hw.trans (add_le_add hL hH)
  simpa only [coefficientError, weight, RecoveryMomentTail.coefficient, add_div] using hh

/-- Full untruncated weighted coefficient error; n≥24 and p≤floor(alpha_d*n)
remain explicit. ell is any fixed natural number, independent of n. -/
theorem coefficient_error (p ell : ℕ) (hp : p≤degree d n) :
    let M := TournamentSkewMargin.branch (BinaryRawGraphWeighted.realGraph (d+1) e B f) v
    Summable (coefficientError (normalized M) (untruncated M p) ell) ∧
      (∑' k, coefficientError (normalized M) (untruncated M p) ell k)≤
        errorConstant d p ell/(n : ℝ)^(p+1) := by
  let M := TournamentSkewMargin.branch (BinaryRawGraphWeighted.realGraph (d+1) e B f) v
  have h := WeightedRecoveryClosure.global_bound (normalized M) (untruncated M p) ell (degree d n)
    ((lowConstant d p ell+highConstant d p ell)/(n : ℝ)^(p+1))
    (actualTailConstant d p ell/(n : ℝ)^(p+1))
    (approximationTailConstant d p ell/(n : ℝ)^(p+1))
    (window_error hn d e B hB he f v hv p ell hp)
    (polynomial_tail hn d e B hB he f v hv p ell)
    (fun E hE => approximation_tail hn d e B hB he f v hv p ell E hE)
  refine ⟨h.1, ?_⟩
  convert h.2 using 1 <;> unfold errorConstant <;> ring

/-- The untruncated actual approximation has every fixed absolute coefficient
moment finite; divergent tsums are not used as norm certificates. -/
theorem weighted_summable (p ell : ℕ) (hp : p≤degree d n) :
    let M := TournamentSkewMargin.branch (BinaryRawGraphWeighted.realGraph (d+1) e B f) v
    Summable (fun k => weight ell k*‖(untruncated M p).coeff k‖) := by
  have h := coefficient_error hn d e B hB he f v hv p ell hp
  exact WeightedRecoveryClosure.approximation_weight_summable _ _ ell h.1

/-- z=1 derivative-ready interface in coefficient form. This is not yet an
analytic iteratedDeriv theorem for the untruncated evaluation function. -/
theorem derivative_coefficients_at_one (p ell : ℕ) (hp : p≤degree d n) :
    let M := TournamentSkewMargin.branch (BinaryRawGraphWeighted.realGraph (d+1) e B f) v
    Summable (fun k => (k.descFactorial ell : ℂ)*(untruncated M p).coeff k) ∧
      ‖fallingFactorialSum (normalized M).coeff ell-
        fallingFactorialSum (fun k => (untruncated M p).coeff k) ell‖≤errorConstant d p ell/(n : ℝ)^(p+1) := by
  have h := coefficient_error hn d e B hB he f v hv p ell hp
  exact WeightedRecoveryClosure.falling_factorial_error _ _ ell _ h.1 h.2
end Graph
end ActualWeightedUntruncatedRecovery
#print axioms ActualWeightedUntruncatedRecovery.coefficient_error
#print axioms ActualWeightedUntruncatedRecovery.derivative_coefficients_at_one

#print axioms ActualWeightedUntruncatedRecovery.weighted_summable
