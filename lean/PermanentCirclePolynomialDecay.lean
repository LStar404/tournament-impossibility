import PermanentPolynomialCircleTail
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Order.Floor.Semiring

/-! Uncompiled scalar tail draft. Explicit constants avoid any hidden
asymptotic premise or reliance on a proxy generating function. -/
noncomputable section
namespace PermanentCirclePolynomialDecay

lemma sqrt_absorption {x c : ℝ} (hx : 0 ≤ x) (hc : 0 < c) (b : ℝ) :
    b * Real.sqrt x ≤ c*x/2 + b^2/(2*c) := by
  have hs := Real.sq_sqrt hx
  have hy := sq_nonneg (c * Real.sqrt x - b)
  have hsc : c^2*(Real.sqrt x)^2=c^2*x := congrArg (fun y : ℝ => c^2*y) hs
  have hd : b * Real.sqrt x - c*x/2 ≤ b^2/(2*c) := by
    apply (le_div_iff₀ (by positivity : 0 < 2*c)).mpr
    nlinarith [hsc]
  linarith

lemma exp_negative_le_inverse_power (p : ℕ) {t : ℝ} (ht : 0 < t) :
    Real.exp (-t) ≤ (p.factorial : ℝ) / t^p := by
  have hf : (0 : ℝ) < p.factorial := by positivity
  have hp : 0 < t^p/(p.factorial : ℝ) := by positivity
  have h := one_div_le_one_div_of_le hp (Real.pow_div_factorial_le_exp t ht.le p)
  simpa only [Real.exp_neg, one_div, inv_div] using h

/-- Explicit all-positive-x domination, with a constant depending only on a,b,c,p. -/
theorem sqrt_exponential_decay (a b : ℝ) {c x : ℝ}
    (hc : 0 < c) (hx : 0 < x) (p : ℕ) :
    Real.exp (a+b*Real.sqrt x-c*x) ≤
      (Real.exp (a+b^2/(2*c)) * (p.factorial : ℝ) / (c/2)^p) / x^p := by
  have hy := sqrt_absorption hx.le hc b
  have he : a+b*Real.sqrt x-c*x ≤ (a+b^2/(2*c)) + -(c*x/2) := by linarith
  calc
    _ ≤ Real.exp ((a+b^2/(2*c)) + -(c*x/2)) := Real.exp_le_exp.mpr he
    _ = Real.exp (a+b^2/(2*c)) * Real.exp (-(c*x/2)) := Real.exp_add _ _
    _ ≤ Real.exp (a+b^2/(2*c)) * ((p.factorial : ℝ)/(c*x/2)^p) :=
      mul_le_mul_of_nonneg_left (exp_negative_le_inverse_power p (by positivity))
        (Real.exp_pos _).le
    _ = _ := by rw [show c*x/2 = (c/2)*x by ring, mul_pow]; ring

/-- A linear coefficient cutoff converts the true exp(a+b sqrt(n)) circle
bound into an explicit arbitrary inverse power. The slack d includes floor loss. -/
theorem circle_linear_cutoff_decay (a b : ℝ) {R δ d : ℝ}
    (hR : 1 < R) (hδ : 0 < δ) (n m p : ℕ) (hn : 0 < n)
    (hm : δ*(n : ℝ)-d ≤ (m : ℝ)) :
    Real.exp (a+b*Real.sqrt (n : ℝ)) / R^m ≤
      (Real.exp (a+d*Real.log R+b^2/(2*(δ*Real.log R))) *
        (p.factorial : ℝ) / ((δ*Real.log R)/2)^p) / (n : ℝ)^p := by
  have hRp : 0 < R := zero_lt_one.trans hR
  have hl : 0 < Real.log R := Real.log_pos hR
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : 0 < δ*Real.log R := mul_pos hδ hl
  have hpow : R^m = Real.exp ((m : ℝ)*Real.log R) := by
    rw [Real.exp_nat_mul, Real.exp_log hRp]
  have hml := mul_le_mul_of_nonneg_right hm hl.le
  calc
    _ = Real.exp (a+b*Real.sqrt (n : ℝ)-(m : ℝ)*Real.log R) := by
      rw [hpow, Real.exp_sub]
    _ ≤ Real.exp ((a+d*Real.log R)+b*Real.sqrt (n : ℝ)-(δ*Real.log R)*(n : ℝ)) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    _ ≤ _ := sqrt_exponential_decay (a+d*Real.log R) b hc hnR p

/-- The natural floor cutoff loses only one geometric factor, already present
in the explicit constant. -/
theorem circle_floor_cutoff_decay (a b : ℝ) {R δ : ℝ}
    (hR : 1 < R) (hδ : 0 < δ) (n p : ℕ) (hn : 0 < n) :
    Real.exp (a+b*Real.sqrt (n : ℝ)) / R^(⌊δ*(n : ℝ)⌋₊) ≤
      (Real.exp (a+Real.log R+b^2/(2*(δ*Real.log R))) *
        (p.factorial : ℝ) / ((δ*Real.log R)/2)^p) / (n : ℝ)^p := by
  have hf := Nat.lt_floor_add_one (δ*(n : ℝ))
  simpa only [one_mul] using circle_linear_cutoff_decay a b hR hδ n
    (⌊δ*(n : ℝ)⌋₊) p hn (show δ*(n : ℝ)-1 ≤ (⌊δ*(n : ℝ)⌋₊ : ℝ) by linarith)

/-- Transfer for the actual permanent polynomial, with an explicit floor cutoff.
The preceding genuine circle-envelope theorem supplies `hcircle` in applications. -/
theorem actual_permanent_floor_tail {N : ℕ}
    (P M : Matrix (Fin N) (Fin N) ℂ) (a b : ℝ) {R δ D : ℝ}
    (hR : 1 < R) (hδ : 0 < δ) (hD : 0 ≤ D) (hN : 0 < N) (p : ℕ)
    (hcircle : ∀ z : ℂ, ‖z‖ = R →
      ‖Matrix.permanent (P+z • M)‖ ≤ D*Real.exp (a+b*Real.sqrt (N : ℝ))) :
    (∑ k ∈ (PermanentPolynomialCircleTail.permanentPolynomial P M).support.filter
      (fun k => ⌊δ*(N : ℝ)⌋₊ < k),
      ‖(PermanentPolynomialCircleTail.permanentPolynomial P M).coeff k‖) ≤
      (R/(R-1)*D) *
      ((Real.exp (a+Real.log R+b^2/(2*(δ*Real.log R))) *
        (p.factorial : ℝ) / ((δ*Real.log R)/2)^p) / (N : ℝ)^p) := by
  have ht := PermanentPolynomialCircleTail.actual_permanent_tail P M R
    (D*Real.exp (a+b*Real.sqrt (N : ℝ))) hR
    (mul_nonneg hD (Real.exp_pos _).le) hcircle (⌊δ*(N : ℝ)⌋₊)
  have hc : 0 ≤ R/(R-1)*D :=
    mul_nonneg (div_nonneg (zero_lt_one.trans hR).le (sub_pos.mpr hR).le) hD
  calc
    _ ≤ R/(R-1)*(D*Real.exp (a+b*Real.sqrt (N : ℝ)))/R^(⌊δ*(N : ℝ)⌋₊) := ht
    _ = (R/(R-1)*D)*(Real.exp (a+b*Real.sqrt (N : ℝ))/R^(⌊δ*(N : ℝ)⌋₊)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (circle_floor_cutoff_decay a b hR hδ N p hN) hc

end PermanentCirclePolynomialDecay
#print axioms PermanentCirclePolynomialDecay.sqrt_exponential_decay
#print axioms PermanentCirclePolynomialDecay.circle_floor_cutoff_decay
#print axioms PermanentCirclePolynomialDecay.actual_permanent_floor_tail
