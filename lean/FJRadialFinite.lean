import Mathlib

/-!
Standalone abstract backend component. Final evidence: focused/result.json.
No repository source or entry point is changed.
These are coefficient-side F/J interfaces and finite resonance calculations.
This module does NOT assert F or J for normalized tournament extremal counts.
The analytic F/J-to-R theorem is not asserted without a proof.
-/
noncomputable section
open Filter Topology Finset
namespace FJRadialFinite

def valuationClass (s n : ℕ) : Prop :=
  2 ^ s ∣ n ∧ ¬ 2 ^ (s + 1) ∣ n

def inverseJet (c : ℕ → ℂ) (d n : ℕ) : ℂ :=
  ∑ j ∈ range (d + 1), c j / (n : ℂ) ^ j

/-- Only positive indices enter F. Coefficients may initially depend on d;
no global convergent power series for a is postulated. -/
def FixedValuationExpansion (a : ℕ → ℂ) : Prop :=
  ∀ s d : ℕ, ∃ c : ℕ → ℂ, ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ,
    ∀ n : ℕ, N ≤ n → 0 < n → valuationClass s n →
      ‖a n - inverseJet c d n‖ ≤ C / (n : ℝ) ^ (d + 1)

/-- The polynomial consequence of analytic J; all multiples are required.
This is weaker than the analytic-common-function version of J and sufficient
for the radial conclusion at the one fixed level r. -/
def UniformJumpAt (a : ℕ → ℂ) (r : ℕ) (κ : ℂ) : Prop :=
  ∃ c : ℕ → ℂ, ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ,
    ∀ n : ℕ, N ≤ n → 0 < n → 2 ^ r ∣ n →
      ‖a n - (inverseJet c (2*r+1) n -
        if 2 ^ (r+1) ∣ n then κ / (n : ℂ) ^ (2*r+1) else 0)‖
        ≤ C / (n : ℝ) ^ (2*r+2)

/-- Single-level coefficient target of the finite gluing step.
All u_j have period b. Only the explicitly displayed pulse has period 2b. -/
def PeriodicJumpJet (a : ℕ → ℂ) (b k : ℕ) (κ : ℂ) : Prop :=
  ∃ u : ℕ → ℕ → ℂ, (∀ j ≤ k+1, Function.Periodic (u j) b) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ,
      ∀ n : ℕ, N ≤ n → 0 < n →
        ‖a n - ((∑ j ∈ range (k+2), u j n / (n : ℂ)^j) -
          if 2*b ∣ n then κ / (n : ℂ)^(k+1) else 0)‖
          ≤ C / (n : ℝ)^(k+2)

/-- Primitive order 2b implies the exact half-period sign, not just norm one. -/
theorem primitive_half_power {b : ℕ} (hb : 0 < b) {ω : ℂ}
    (hω : IsPrimitiveRoot ω (2*b)) : ω ^ b = -1 := by
  have h : IsPrimitiveRoot (ω ^ b) 2 :=
    IsPrimitiveRoot.pow (by omega : 0 < 2*b) hω (by omega : 2*b=b*2)
  exact h.eq_neg_one_of_two_right

/-- Half-period pairing alone proves the vanishing Fourier coefficient;
full finite Fourier inversion is not needed for this calculation. -/
theorem half_period_sum_zero (u : ℕ → ℂ) (b : ℕ) (ω : ℂ)
    (hu : Function.Periodic u b) (hω : ω ^ b = -1) :
    (∑ n ∈ range (2*b), u n * ω^n) = 0 := by
  rw [show 2*b=b+b by omega, Finset.sum_range_add]
  have hs : (∑ n ∈ range b, u (b+n) * ω^(b+n)) =
      -(∑ n ∈ range b, u n * ω^n) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro n _
    rw [show b+n=n+b by omega, hu n, pow_add, hω]
    ring
  rw [hs]
  ring

/-- With residues 0,...,q-1, the multiples-of-q pulse has Fourier sum κ. -/
theorem pulse_sum (q : ℕ) (hq : 0 < q) (κ ω : ℂ) :
    (∑ n ∈ range q, (if q ∣ n then κ else 0) * ω^n) = κ := by
  classical
  rw [Finset.sum_eq_single 0]
  · simp
  · intro n hn hn0
    have hnot : ¬ q ∣ n := by
      intro hd
      exact hn0 (Nat.eq_zero_of_dvd_of_lt hd (Finset.mem_range.mp hn))
    simp [hnot]
  · intro hz
    exact False.elim (hz (Finset.mem_range.mpr hq))

/-- The sign and normalization of the first resonance. The 0 residue here
represents the q residue in sums over 1,...,q. -/
theorem first_resonance (u : ℕ → ℂ) {b : ℕ} (hb : 0 < b) (κ ω : ℂ)
    (hu : Function.Periodic u b) (hω : IsPrimitiveRoot ω (2*b)) :
    ((∑ n ∈ range (2*b),
      (u n - if 2*b ∣ n then κ else 0) * ω^n) / (2*b : ℕ)) =
      -κ / (2*b : ℕ) := by
  have hc := half_period_sum_zero u b ω hu (primitive_half_power hb hω)
  have hp := pulse_sum (2*b) (by omega) κ ω
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  rw [hc, hp, zero_sub]

#print axioms FJRadialFinite.primitive_half_power
#print axioms FJRadialFinite.half_period_sum_zero
#print axioms FJRadialFinite.first_resonance
end FJRadialFinite
