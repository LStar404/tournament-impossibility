import Mathlib

/-! Finite color-word energy and algebraic repair budgets.
No assertion about tournament realization or actual swap distance is made here. -/
namespace ColorEnergy
open Finset

/-- The squared row-score expression for a color word and its prefix sums. -/
def energy (n : ℕ) (A : ℝ) (P c : ℕ → ℝ) : ℝ :=
  ∑ i ∈ range n, (A - 2 * P i - c i)^2

def baseEnergy (n : ℕ) (A : ℝ) (P : ℕ → ℝ) : ℝ :=
  ∑ i ∈ range n, (A - 2 * P i)^2

/-- Telescoping identity, before imposing that A is the final prefix. -/
theorem energy_telescope (n : ℕ) (A : ℝ) (P c : ℕ → ℝ)
    (h0 : P 0 = 0)
    (hstep : ∀ i < n, P (i + 1) = P i + c i)
    (hcolor : ∀ i < n, (c i)^2 = 1) :
    energy n A P c = baseEnergy n A P + 2 * (P n)^2 - 2 * A * P n - n := by
  induction n with
  | zero => simp [energy, baseEnergy, h0]
  | succ n ih =>
    have ih' := ih (fun i hi => hstep i (by omega)) (fun i hi => hcolor i (by omega))
    have hs := hstep n (by omega)
    have hc := hcolor n (by omega)
    simp only [energy, baseEnergy, sum_range_succ] at ih' ⊢
    rw [Nat.cast_add, Nat.cast_one, ih', hs]
    nlinarith [hc]

/-- For a genuine color word A = P n, the boundary terms cancel. -/
theorem energy_identity (n : ℕ) (P c : ℕ → ℝ)
    (h0 : P 0 = 0)
    (hstep : ∀ i < n, P (i + 1) = P i + c i)
    (hcolor : ∀ i < n, (c i)^2 = 1) :
    energy n (P n) P c = baseEnergy n (P n) P - n := by
  rw [energy_telescope n (P n) P c h0 hstep hcolor]
  ring

/-- Odd normalization: the energy is four times the prefix quadratic cost. -/
theorem odd_energy (n : ℕ) (P c : ℕ → ℝ)
    (h0 : P 0 = 0) (hfinal : P n = 1)
    (hstep : ∀ i < n, P (i + 1) = P i + c i)
    (hcolor : ∀ i < n, (c i)^2 = 1) :
    energy n 1 P c = 4 * ∑ i ∈ range n, P i * (P i - 1) := by
  have he := energy_identity n P c h0 hstep hcolor
  rw [hfinal] at he
  rw [he]
  unfold baseEnergy
  have hp : ∀ i, (1 - 2 * P i)^2 = 4 * (P i * (P i - 1)) + 1 := by intro i; ring
  simp_rw [hp]
  simp [sum_add_distrib, ← mul_sum]

/-- Integer discreteness, crucial to the repair estimate. -/
theorem int_abs_le_sq (z : ℤ) : |z| ≤ z^2 := by
  have ha := abs_nonneg z
  have hsq : |z|^2 = z^2 := sq_abs z
  by_cases hz : |z| = 0
  · nlinarith
  · have hh : 1 ≤ |z| := by omega
    nlinarith

/-- At an even prefix p = 2k the target prefix is zero. -/
theorem even_prefix_budget (k : ℤ) : 2 * |2 * k| ≤ (2 * k)^2 := by
  have h := int_abs_le_sq k
  rw [abs_mul]
  norm_num
  nlinarith

/-- At an odd prefix the target is its sign. This is the exact local cost bound. -/
theorem odd_prefix_budget (p : ℤ) (hp : p ≠ 0) :
    2 * (|p| - 1) ≤ p^2 - 1 := by
  have ha : 1 ≤ |p| := by have := abs_pos.mpr hp; omega
  have hs : |p|^2 = p^2 := sq_abs p
  nlinarith [sq_nonneg (|p| - 1)]

/-- Sum of local repair costs is at most one quarter of the quadratic excess.
The hypotheses specify the local costs; identifying their half-sum with the
minimum number of adjacent swaps is a separate, unformalized transport lemma. -/
theorem summed_repair_budget {ι : Type*} (s : Finset ι) (d q : ι → ℝ)
    (hlocal : ∀ i ∈ s, 2 * d i ≤ q i) :
    (∑ i ∈ s, d i) / 2 ≤ (4 * ∑ i ∈ s, q i) / 16 := by
  have h := sum_le_sum hlocal
  rw [← mul_sum] at h
  linarith

/-- Even normalization, with no hidden parity or matrix assumption. -/
theorem even_energy (n : ℕ) (P c : ℕ → ℝ)
    (h0 : P 0 = 0) (hfinal : P n = 0)
    (hstep : ∀ i < n, P (i + 1) = P i + c i)
    (hcolor : ∀ i < n, (c i)^2 = 1) :
    energy n 0 P c = 4 * (∑ i ∈ range n, (P i)^2) - n := by
  have he := energy_identity n P c h0 hstep hcolor
  rw [hfinal] at he
  rw [he]
  unfold baseEnergy
  have hp : ∀ i, (0 - 2 * P i)^2 = 4 * (P i)^2 := by intro i; ring
  simp_rw [hp]
  rw [mul_sum]

/-- Odd-normalized repair cost at an even prefix. -/
theorem odd_repair_even_prefix (k : ℤ) :
    |2 * k| ≤ (2 * k) * (2 * k - 1) := by
  have h := int_abs_le_sq k
  have hle := le_abs_self k
  rw [abs_mul]
  norm_num
  nlinarith

/-- Odd-normalized repair cost at an odd prefix (target prefix 1). -/
theorem odd_repair_odd_prefix (k : ℤ) :
    |(2 * k + 1) - 1| ≤ (2 * k + 1) * ((2 * k + 1) - 1) := by
  have h := int_abs_le_sq k
  have hle := neg_le_abs k
  have he : (2 * k + 1) - 1 = 2 * k := by ring
  rw [he, abs_mul]
  norm_num
  nlinarith

/-- An explicit finite prefix transport budget in the odd normalization.
The target is 0 at even prefixes and 1 at odd prefixes, encoded by the two
parity alternatives. This does not assert attainability by swaps. -/
theorem odd_prefix_transport_budget {ι : Type*} (s : Finset ι)
    (P target : ι → ℤ)
    (hparity : ∀ i ∈ s,
      (∃ k : ℤ, P i = 2 * k ∧ target i = 0) ∨
      (∃ k : ℤ, P i = 2 * k + 1 ∧ target i = 1)) :
    (∑ i ∈ s, |P i - target i|) ≤ ∑ i ∈ s, P i * (P i - 1) := by
  apply sum_le_sum
  intro i hi
  rcases hparity i hi with ⟨k, hp, ht⟩ | ⟨k, hp, ht⟩
  · rw [hp, ht, sub_zero]
    exact odd_repair_even_prefix k
  · rw [hp, ht]
    exact odd_repair_odd_prefix k

#print axioms even_energy
#print axioms odd_prefix_transport_budget
#print axioms energy_telescope
#print axioms energy_identity
#print axioms odd_energy
#print axioms even_prefix_budget
#print axioms odd_prefix_budget
#print axioms summed_repair_budget
end ColorEnergy
