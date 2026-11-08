import ColorTransportExact
import DiamondGap
import ColorTransport
import ColorEnergy
import OrderedCancellation
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

/-! Local packet endpoint: finite low-position packets of length 2^q,
remaining recursion depth r-q. No assertion about tournament kernels or R. -/
example {R : Type*} [Ring R] (F : OrderedCancellation.Filtration R)
    (p m : List R) (hp : ∀ x ∈ p, F.mem 1 (x - 1))
    (hm : ∀ x ∈ m, F.mem 1 (x - 1)) (hz : F.mem 1 0)
    (r q : ℕ) (hq : q ≤ r) (lp : p.length = 2 ^ q) (lm : m.length = 2 ^ q) :
    F.mem (r - q + 1)
      ((OrderedCancellation.expandPackets p m (OrderedCancellation.words (r - q)).1).prod -
       (OrderedCancellation.expandPackets p m (OrderedCancellation.words (r - q)).2).prod) :=
  OrderedCancellation.packet_difference_order F p m hp hm hz r q hq lp lm

#print axioms OrderedCancellation.difference_order
#print axioms OrderedCancellation.evaluate_words
#print axioms OrderedCancellation.blocks_add
#print axioms OrderedCancellation.packet_length
#print axioms OrderedCancellation.packet_difference_order

/-! Finite prefix-energy endpoint only. No graph realization, attainable swap
sequence, or graph-edit upper bound follows from this example alone. -/
example (n : ℕ) (P c : ℕ → ℝ) (h0 : P 0 = 0) (hfinal : P n = 1)
    (hstep : ∀ i < n, P (i + 1) = P i + c i)
    (hcolor : ∀ i < n, (c i)^2 = 1) :
    ColorEnergy.energy n 1 P c = 4 * ∑ i ∈ Finset.range n, P i * (P i - 1) :=
  ColorEnergy.odd_energy n P c h0 hfinal hstep hcolor

#print axioms ColorEnergy.energy_telescope
#print axioms ColorEnergy.energy_identity
#print axioms ColorEnergy.even_energy
#print axioms ColorEnergy.odd_energy
#print axioms ColorEnergy.summed_repair_budget
#print axioms ColorEnergy.odd_prefix_transport_budget

/-! Actual adjacent unlike-color swap reachability and only a lower bound on
minimum distance. No equality or graph-edit upper bound is asserted. -/
example (u v : List Bool) (hlen : u.length = v.length)
    (hc : ColorTransport.charge u = ColorTransport.charge v) :
    ∃ n, ColorTransport.Swaps n u v ∧
      (∀ m, ColorTransport.Swaps m u v → n ≤ m) ∧
      ColorTransport.area u v ≤ (n : ℤ) :=
  ColorTransport.minimum_swaps_exists hlen hc

#print axioms ColorTransport.equal_total_reachable
#print axioms ColorTransport.reaches_paired
#print axioms ColorTransport.reaches_alternatingOdd
#print axioms ColorTransport.area_le_swaps
#print axioms ColorTransport.minimum_swaps_exists

/-! Finite tournament combinatorics only: the count is of unordered four-sets.
This endpoint supplies no asymptotic recovery or Condition R implication. -/
example {V : Type*} [DecidableEq V] [Fintype V]
    (T : DiamondGap.Tournament V) :
    T.diamonds.card = 0 ∨ Fintype.card V ≤ 4 * T.diamonds.card :=
  T.zero_or_gap

#print axioms DiamondGap.Tournament.quad_iff_pattern
#print axioms DiamondGap.Tournament.diamond_covers
#print axioms DiamondGap.Tournament.positive_gap
#print axioms DiamondGap.Tournament.zero_or_gap

/-! Attained color-word repair bounds; matrix identification and conversion
of a word swap into a graph edge reversal remain separate obligations. -/
example (w : List Bool) (k : ℕ) (hl : w.length = 2*k+1)
    (hc : ColorTransport.charge w = 1) :
    ∃ n, ColorTransport.Swaps n w (ColorTransport.alternatingOdd k) ∧
      (n : ℝ) ≤ ColorTransport.wordEnergy w / 8 :=
  ColorTransport.odd_energy_repair w k hl hc

example (w : List Bool) (k : ℕ) (hl : w.length = 2*k)
    (hc : ColorTransport.charge w = 0) :
    ∃ n, ColorTransport.Swaps n w
      (ColorTransport.paired (ColorTransport.repairOrient w k)) ∧
      (n : ℝ) ≤ (ColorTransport.wordEnergy w - w.length) / 16 :=
  ColorTransport.even_energy_repair w k hl hc

#print axioms ColorTransport.area_descent
#print axioms ColorTransport.exact_swaps
#print axioms ColorTransport.exact_minimum
#print axioms ColorTransport.prefix_area_identity
#print axioms ColorTransport.prefix_exact_minimum
#print axioms ColorTransport.odd_energy_repair
#print axioms ColorTransport.even_energy_repair
