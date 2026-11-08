import QRegularApplications
import PathCountGrowth
import QRegularRationalLimit

/-! Independent endpoint checks. These examples pin the public statements to
actual tournament quantities and to the full q-kernel, not a substituted
matrix-representation predicate or a presumed obstruction. -/
open Filter Topology
namespace NonAlgebraicity.EndpointCheck

example (q : ℕ) (a : ℕ → ℂ) :
    IsQRegular q a ↔ FiniteDimensional ℂ
      (Submodule.span ℂ {f : ℕ → ℂ | ∃ e r : ℕ,
        r < q ^ e ∧ f = fun n => a (q ^ e * n + r)}) := Iff.rfl

example (q : ℕ) (hq : 2 ≤ q) (a : ℕ → ℚ) (L : ℂ)
    (hlim : Tendsto (fun n => (a n : ℂ)) atTop (𝓝 L))
    (hL : Transcendental ℚ L) :
    ¬ IsQRegular q (fun n => (a n : ℂ)) :=
  not_qRegular_of_transcendental_limit q hq a L hlim hL

example (q : ℕ) (hq : 2 ≤ q) (a : ℕ → ℚ) (k : ℕ) (L : ℂ)
    (hlim : Tendsto (fun n => ((a n / (n : ℚ)^k : ℚ) : ℂ)) atTop (𝓝 L))
    (hL : Transcendental ℚ L) :
    ¬ IsQRegular q (fun n => (a n : ℂ)) :=
  not_qRegular_of_scaled_transcendental_limit q hq a k L hlim hL

example (q : ℕ) (hq : 2 ≤ q)
    (asymptotic : ExtremalAsymptotic) (lw : FourExponentialIndependence) :
    ¬ IsQRegular q (fun n => (normalizedCoefficient n : ℂ)) :=
  normalizedCoefficient_not_qRegular q hq asymptotic lw

example (q : ℕ) (hq : 2 ≤ q)
    (asymptotic : ExtremalAsymptotic) (lw : FourExponentialIndependence) :
    ¬ IsQRegular q (fun n => (halfScaleRemainder n : ℂ)) :=
  halfScaleRemainder_not_qRegular q hq asymptotic lw

example (asymptotic : ExtremalAsymptotic) :
    ¬ ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      ∀ n, (maximalPathCount n : ℝ) ≤ C * D^n :=
  maximalPathCount_not_exponentially_bounded asymptotic

example (asymptotic : ExtremalAsymptotic)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (q : ℕ) (hq : 2 ≤ q) (A : Fin q → E →L[ℂ] E)
    (V : ℕ → E) (f : E →L[ℂ] ℂ)
    (hV : ∀ n, n ≠ 0 → V n = A ⟨n % q, Nat.mod_lt n (by omega)⟩ (V (n / q)))
    (hout : ∀ n, (maximalPathCount n : ℂ) = f (V n)) : False :=
  maximalPathCount_no_linear_digit_representation asymptotic q hq A V f hV hout

/-- Full Appendix A.5, directly stated using the entire q-kernel span.
No graph asymptotic, transcendence input, or rationality premise is required. -/
example (q : ℕ) (hq : 2 ≤ q) (a : ℕ → ℚ) (k : ℕ) (L : ℂ)
    (ha : FiniteDimensional ℂ
      (Submodule.span ℂ {f : ℕ → ℂ | ∃ e r : ℕ,
        r < q ^ e ∧ f = fun n => (a (q ^ e * n + r) : ℂ)}))
    (hlim : Tendsto (fun n => ((a n / (n : ℚ)^k : ℚ) : ℂ)) atTop (𝓝 L)) :
    ∃ r : ℚ, (r : ℂ) = L :=
  qRegular_scaled_limit_rational q hq a k L ha hlim

example (q : ℕ) (hq : 2 ≤ q) (a : ℕ → ℚ) (L : ℂ)
    (ha : IsQRegular q (fun n => (a n : ℂ)))
    (hlim : Tendsto (fun n => (a n : ℂ)) atTop (𝓝 L)) :
    ∃ r : ℚ, (r : ℂ) = L :=
  qRegular_limit_rational q hq a L ha hlim

end NonAlgebraicity.EndpointCheck

#print axioms NonAlgebraicity.qRegular_power_representation
#print axioms NonAlgebraicity.matrix_output_series_relation
#print axioms NonAlgebraicity.not_qRegular_of_transcendental_limit
#print axioms NonAlgebraicity.not_qRegular_of_scaled_transcendental_limit
#print axioms NonAlgebraicity.normalizedCoefficient_not_qRegular
#print axioms NonAlgebraicity.halfScaleRemainder_not_qRegular
#print axioms NonAlgebraicity.digit_recursion_exponential_bound
#print axioms NonAlgebraicity.maximalPathCount_not_exponentially_bounded
#print axioms NonAlgebraicity.maximalPathCount_no_linear_digit_representation

#print axioms NonAlgebraicity.qRegular_scaled_limit_rational
#print axioms NonAlgebraicity.qRegular_limit_rational
