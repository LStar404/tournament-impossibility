import ActivityFactorialMultiplier

/-!
Finite-window factorial error after multiplying by the actual core.
This is deliberately conditional on the actual core's weighted norm bound.
It does not turn the diamond-free core theorem into an arbitrary-depth theorem.
-/
noncomputable section
namespace CoreActivityFactorialBridge
open WeightedCoefficientNorm

/-- Multiplying by the core before applying the factorial multiplier is essential.
The recovery operator is not multiplicative. -/
theorem product_order_bound (n p j : ℕ) (hn : 0 < n) (hj : j ≤ p)
    (G Cj : PowerSeries ℂ) (E : Finset ℕ)
    (r s sigma B L : ℝ) (hr : 0 ≤ r) (hs : 0 < s)
    (hsigma : 1 < sigma) (hgap : sigma * r < s) (hL : 0 ≤ L)
    (hG : Finite s G) (hCj : Finite s Cj)
    (hbG : norm s G ≤ B) (hbCj : norm s Cj ≤ L / (n : ℝ)^j)
    (hE : ∀ k ∈ E, 2*k ≤ n ∧ (k : ℝ)/(n : ℝ) ≤ Real.log sigma) :
    ActivityFactorialMultiplier.error n (p-j) (G*Cj) E r ≤
      (WeightedPolynomialMultiplier.moment (sigma*r/s) (2*(p-j+1)) *
        (B*L)) / (n : ℝ)^(p+1) := by
  have hGC : Finite s (G*Cj) := finite_mul hs.le hG hCj
  have hbound : norm s (G*Cj) ≤ (B*L)/(n : ℝ)^j := by
    calc
      _ ≤ norm s G * norm s Cj := mul_bound hs.le hG hCj
      _ ≤ norm s G * (L/(n : ℝ)^j) :=
        mul_le_mul_of_nonneg_left hbCj (norm_nonnegative hs.le G)
      _ ≤ B * (L/(n : ℝ)^j) :=
        mul_le_mul_of_nonneg_right hbG
          (div_nonneg hL (pow_nonneg (Nat.cast_nonneg n) j))
      _ = _ := by ring
  exact ActivityFactorialMultiplier.order_bound n p j hn hj (G*Cj) E r s sigma
    (B*L) hr hs hsigma hgap hGC hbound hE

/-- C0=1 leaves the CORE as the j=0 summand. Its multiplier error is generally
nonzero; it must not be discarded using the bare-activity `zero_activity` lemma. -/
theorem zeroth_order_bound (n p : ℕ) (hn : 0 < n)
    (G : PowerSeries ℂ) (E : Finset ℕ)
    (r s sigma B : ℝ) (hr : 0 ≤ r) (hs : 0 < s)
    (hsigma : 1 < sigma) (hgap : sigma*r < s)
    (hG : Finite s G) (hbG : norm s G ≤ B)
    (hE : ∀ k ∈ E, 2*k ≤ n ∧ (k : ℝ)/(n : ℝ) ≤ Real.log sigma) :
    ActivityFactorialMultiplier.error n p G E r ≤
      (WeightedPolynomialMultiplier.moment (sigma*r/s) (2*(p+1))*B) /
        (n : ℝ)^(p+1) := by
  simpa using ActivityFactorialMultiplier.order_bound n p 0 hn (Nat.zero_le p)
    G E r s sigma B hr hs hsigma hgap hG (by simpa using hbG) hE

end CoreActivityFactorialBridge

#print axioms CoreActivityFactorialBridge.product_order_bound
#print axioms CoreActivityFactorialBridge.zeroth_order_bound
