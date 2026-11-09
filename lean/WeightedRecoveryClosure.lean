import RecoveryMomentTail

/-! Closure from finite weighted coefficient bounds to
absolute summability and the falling-factorial coefficient-sum interface at 1.
No equality with analytic iteratedDeriv is asserted in this module. -/
noncomputable section
namespace WeightedRecoveryClosure

abbrev weight (ell k : ℕ) : ℝ := (k : ℝ)^ell

def coefficientError (P : Polynomial ℂ) (U : PowerSeries ℂ) (ell k : ℕ) : ℝ :=
  weight ell k*‖P.coeff k-U.coeff k‖

lemma weight_nonneg (ell k : ℕ) : 0≤weight ell k := by unfold weight; positivity

lemma sum_restrict (E S : Finset ℕ) (f : ℕ → ℝ) (hf : ∀ k, 0≤f k)
    (hz : ∀ k∈E, k∉S → f k=0) : (∑ k∈E, f k)≤∑ k∈S, f k := by
  classical
  calc
    _ = ∑ k∈E∩S, f k := by
      symm
      apply Finset.sum_subset Finset.inter_subset_left
      intro k hk hnot
      apply hz k hk
      intro hs
      exact hnot (Finset.mem_inter.mpr ⟨hk, hs⟩)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun k hk hnot => hf k)

/-- Full coefficient bound, not just a polynomial-window norm. -/
theorem global_bound (P : Polynomial ℂ) (U : PowerSeries ℂ) (ell m : ℕ) (A B C : ℝ)
    (hlow : (∑ k∈Finset.range (m+1), coefficientError P U ell k)≤A)
    (hpoly : (∑ k∈P.support.filter (fun k => m<k), weight ell k*‖P.coeff k‖)≤B)
    (htail : ∀ E : Finset ℕ, (∀ k∈E, m<k) →
      (∑ k∈E, weight ell k*‖U.coeff k‖)≤C) :
    Summable (coefficientError P U ell) ∧ (∑' k, coefficientError P U ell k)≤A+B+C := by
  classical
  have hn (k : ℕ) : 0≤coefficientError P U ell k :=
    mul_nonneg (weight_nonneg ell k) (norm_nonneg _)
  have hb (E : Finset ℕ) : (∑ k∈E, coefficientError P U ell k)≤A+B+C := by
    let lo := E.filter (fun k => k≤ m)
    let hi := E.filter (fun k => ¬k≤ m)
    have hlo : (∑ k∈lo, coefficientError P U ell k)≤A := by
      apply (Finset.sum_le_sum_of_subset_of_nonneg (show lo⊆Finset.range (m+1) by
        intro k hk; have hh := (Finset.mem_filter.mp hk).2; simpa using hh)
        (fun k hk hnot => hn k)).trans hlow
    have hhi : ∀ k∈hi, m<k := by
      intro k hk
      exact lt_of_not_ge (Finset.mem_filter.mp hk).2
    have hP : (∑ k∈hi, weight ell k*‖P.coeff k‖)≤B := by
      apply (sum_restrict hi (P.support.filter (fun k => m<k))
        (fun k => weight ell k*‖P.coeff k‖) (fun k => by positivity) ?_).trans hpoly
      intro k hk hnot
      have hz : P.coeff k=0 := by
        by_contra h
        exact hnot (Finset.mem_filter.mpr ⟨Polynomial.mem_support_iff.mpr h, hhi k hk⟩)
      simp [hz]
    have hU := htail hi hhi
    have hH : (∑ k∈hi, coefficientError P U ell k)≤B+C := by
      calc
        _ ≤ ∑ k∈hi, (weight ell k*‖P.coeff k‖+weight ell k*‖U.coeff k‖) := by
          apply Finset.sum_le_sum
          intro k hk
          simpa only [coefficientError, mul_add] using
            mul_le_mul_of_nonneg_left (norm_sub_le (P.coeff k) (U.coeff k)) (weight_nonneg ell k)
        _ ≤ _ := by rw [Finset.sum_add_distrib]; exact add_le_add hP hU
    have hsplit := Finset.sum_filter_add_sum_filter_not E (fun k => k≤ m) (coefficientError P U ell)
    change (∑ k∈lo, coefficientError P U ell k)+(∑ k∈hi, coefficientError P U ell k)=_ at hsplit
    rw [← hsplit]
    linarith
  exact ⟨summable_of_sum_le hn hb, Real.tsum_le_of_sum_le hn hb⟩

lemma polynomial_weight_summable (P : Polynomial ℂ) (ell : ℕ) :
    Summable (fun k => weight ell k*‖P.coeff k‖) := by
  apply summable_of_sum_le (fun k => by positivity)
    (c := ∑ k∈P.support, weight ell k*‖P.coeff k‖)
  intro E
  apply sum_restrict E P.support _ (fun k => by positivity)
  intro k hk hnot
  have hz : P.coeff k=0 := by simpa only [Polynomial.mem_support_iff, not_not] using hnot
  simp [hz]

lemma approximation_weight_summable (P : Polynomial ℂ) (U : PowerSeries ℂ) (ell : ℕ)
    (herror : Summable (coefficientError P U ell)) :
    Summable (fun k => weight ell k*‖U.coeff k‖) := by
  have hp := polynomial_weight_summable P ell
  apply (hp.add herror).of_nonneg_of_le (fun k => by positivity)
  intro k
  have h := norm_le_norm_sub_add (U.coeff k) (P.coeff k)
  rw [norm_sub_rev] at h
  have hh := mul_le_mul_of_nonneg_left h (weight_nonneg ell k)
  simpa only [coefficientError, mul_add, add_comm] using hh

def fallingFactorialSum (a : ℕ → ℂ) (ell : ℕ) : ℂ :=
  ∑' k, (k.descFactorial ell : ℂ)*a k

lemma falling_factorial_norm (a : ℕ → ℂ) (ell k : ℕ) :
    ‖(k.descFactorial ell : ℂ)*a k‖≤weight ell k*‖a k‖ := by
  rw [norm_mul, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact_mod_cast Nat.descFactorial_le_pow k ell

lemma falling_factorial_summable (a : ℕ → ℂ) (ell : ℕ)
    (ha : Summable (fun k => weight ell k*‖a k‖)) :
    Summable (fun k => (k.descFactorial ell : ℂ)*a k) := by
  exact (ha.of_nonneg_of_le (fun k => norm_nonneg _) (falling_factorial_norm a ell)).of_norm

/-- Derivative-ready coefficient interface at z=1. Analytic identification with
iteratedDeriv of the untruncated evaluation function is a separate requirement. -/
theorem falling_factorial_error (P : Polynomial ℂ) (U : PowerSeries ℂ) (ell : ℕ) (K : ℝ)
    (herror : Summable (coefficientError P U ell))
    (hbound : (∑' k, coefficientError P U ell k)≤K) :
    Summable (fun k => (k.descFactorial ell : ℂ)*U.coeff k) ∧
    ‖fallingFactorialSum P.coeff ell-fallingFactorialSum (fun k => U.coeff k) ell‖≤K := by
  have hP := falling_factorial_summable P.coeff ell (polynomial_weight_summable P ell)
  have hU := falling_factorial_summable (fun k => U.coeff k) ell (approximation_weight_summable P U ell herror)
  refine ⟨hU, ?_⟩
  have hn : Summable (fun k => ‖(k.descFactorial ell : ℂ)*(P.coeff k-U.coeff k)‖) :=
    herror.of_nonneg_of_le (fun k => norm_nonneg _) (falling_factorial_norm (fun k => P.coeff k-U.coeff k) ell)
  unfold fallingFactorialSum
  rw [← hP.tsum_sub hU]
  simp only [← mul_sub]
  exact (norm_tsum_le_tsum_norm hn).trans
    ((hn.tsum_le_tsum (falling_factorial_norm (fun k => P.coeff k-U.coeff k) ell) herror).trans hbound)
end WeightedRecoveryClosure
#print axioms WeightedRecoveryClosure.global_bound
#print axioms WeightedRecoveryClosure.falling_factorial_error
