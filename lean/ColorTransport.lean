import Mathlib

/-! Constructive reachability of finite binary color words by adjacent unlike swaps.
This file does not assert the minimum distance/prefix-area formula. -/
namespace ColorTransport

/-- True represents +1 and false represents -1. -/
def charge (w : List Bool) : ℤ := (w.count true : ℤ) - (w.count false : ℤ)

/-- Numeric color attached to a binary letter. -/
def color (a : Bool) : ℤ := if a then 1 else -1

/-- The count-based total really is the sum of the ±1 colors. -/
theorem charge_eq_sum (w : List Bool) : charge w = (w.map color).sum := by
  induction w with
  | nil => simp [charge]
  | cons a w ih => cases a <;> simp_all [charge, color] <;> omega

/-- Removing the first color gives the usual prefix-path increment. -/
theorem charge_cons (a : Bool) (w : List Bool) :
    charge (a :: w) = color a + charge w := by
  simp only [charge_eq_sum, List.map_cons, List.sum_cons]

/-- A derivation with exactly n adjacent unlike-color swaps. `cons` merely
lifts a derivation beneath a fixed first letter and does not add a swap. -/
inductive Swaps : ℕ → List Bool → List Bool → Prop
  | refl (w) : Swaps 0 w w
  | swap (a b : Bool) (w) (h : a ≠ b) : Swaps 1 (a :: b :: w) (b :: a :: w)
  | cons (a : Bool) {n u v} : Swaps n u v → Swaps n (a :: u) (a :: v)
  | trans {m n u v w} : Swaps m u v → Swaps n v w → Swaps (m+n) u w

/-- Each derivation consists solely of permutations. -/
theorem Swaps.perm {n u v} (h : Swaps n u v) : u.Perm v := by
  induction h with
  | refl w => exact List.Perm.refl w
  | swap a b w _ => exact List.Perm.swap b a w
  | cons a _ ih => exact List.Perm.cons a ih
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Permutation equivalence is witnessed by finitely many adjacent unlike swaps. -/
theorem perm_has_swaps {u v : List Bool} (h : u.Perm v) : ∃ n, Swaps n u v := by
  induction h with
  | nil => exact ⟨0, Swaps.refl []⟩
  | cons a _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n, Swaps.cons a hn⟩
  | swap a b w =>
    by_cases hab : b = a
    · subst b
      exact ⟨0, Swaps.refl _⟩
    · exact ⟨1, Swaps.swap b a w hab⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨m, hm⟩ := ih₁
    obtain ⟨n, hn⟩ := ih₂
    exact ⟨m+n, Swaps.trans hm hn⟩

theorem counts_sum_length (w : List Bool) :
    w.count true + w.count false = w.length := by
  induction w with
  | nil => simp
  | cons a w ih => cases a <;> simp <;> omega

/-- For actual binary words, length and total color determine the permutation class. -/
theorem perm_of_length_charge {u v : List Bool}
    (hlen : u.length = v.length) (hc : charge u = charge v) : u.Perm v := by
  apply List.perm_iff_count.mpr
  intro a
  have hu := counts_sum_length u
  have hv := counts_sum_length v
  unfold charge at hc
  cases a <;> omega

/-- The concrete equal-total adjacent-swap reachability theorem. -/
theorem equal_total_reachable {u v : List Bool}
    (hlen : u.length = v.length) (hc : charge u = charge v) :
    ∃ n, Swaps n u v := perm_has_swaps (perm_of_length_charge hlen hc)

/-- A paired target with freely chosen orientation of each adjacent pair. -/
def paired : List Bool → List Bool
  | [] => []
  | a :: rest => a :: (!a) :: paired rest

@[simp] theorem paired_length (orient : List Bool) :
    (paired orient).length = 2 * orient.length := by
  induction orient with
  | nil => simp [paired]
  | cons a rest ih => simp [paired, ih]; omega

@[simp] theorem paired_charge (orient : List Bool) : charge (paired orient) = 0 := by
  induction orient with
  | nil => simp [paired, charge]
  | cons a rest ih => cases a <;> simp_all [paired, charge]

/-- Every even prefix of a paired target has total color zero. -/
theorem paired_even_prefix (orient : List Bool) (k : ℕ) :
    charge ((paired orient).take (2*k)) = 0 := by
  induction orient generalizing k with
  | nil => simp [paired, charge]
  | cons a rest ih =>
    cases k with
    | zero => simp [charge]
    | succ k =>
      have he : 2 * (k+1) = (2*k+1)+1 := by omega
      rw [he]
      simp only [paired, List.take_succ_cons, charge_cons]
      have hc : color a + color (!a) = 0 := by cases a <;> decide
      have ht := ih k
      omega

/-- Every odd prefix of a paired target has exactly the chosen pair color. -/
theorem paired_odd_prefix (orient : List Bool) (k : ℕ) (hk : k < orient.length) :
    charge ((paired orient).take (2*k+1)) = color (orient.getD k false) := by
  induction orient generalizing k with
  | nil => simp at hk
  | cons a rest ih =>
    cases k with
    | zero => cases a <;> simp [paired, charge, color]
    | succ k =>
      have he : 2 * (k+1) + 1 = ((2*k+1)+1)+1 := by omega
      rw [he]
      simp only [paired, List.take_succ_cons, charge_cons, List.getD_cons_succ]
      have hc : color a + color (!a) = 0 := by cases a <;> decide
      have ht := ih k (by simpa using hk)
      omega

/-- Every balanced word reaches any prescribed paired target of the same length. -/
theorem reaches_paired (w orient : List Bool)
    (hlen : w.length = 2 * orient.length) (hc : charge w = 0) :
    ∃ n, Swaps n w (paired orient) := by
  apply equal_total_reachable
  · simpa using hlen
  · simpa using hc

/-- A concrete canonical odd target: + - + - ... +. -/
def alternatingOdd (k : ℕ) : List Bool := true :: paired (List.replicate k false)

@[simp] theorem alternatingOdd_length (k : ℕ) :
    (alternatingOdd k).length = 2*k+1 := by simp [alternatingOdd]

@[simp] theorem alternatingOdd_charge (k : ℕ) : charge (alternatingOdd k) = 1 := by
  have h := paired_charge (List.replicate k false)
  simp only [alternatingOdd, charge, List.count_cons] at *
  simp at *
  omega

/-- Every odd normalized word has an explicitly constructed reachable alternating target. -/
theorem reaches_alternatingOdd (w : List Bool) (k : ℕ)
    (hlen : w.length = 2*k+1) (hc : charge w = 1) :
    ∃ n, Swaps n w (alternatingOdd k) := by
  apply equal_total_reachable
  · simpa using hlen
  · simpa using hc

/-- Suffix-count transport area. For equal-total words it is the same
quantity as the sum of absolute prefix +1-count discrepancies. -/
def area : List Bool → List Bool → ℤ
  | _ :: u, _ :: v => |(u.count true : ℤ) - (v.count true : ℤ)| + area u v
  | _, _ => 0

@[simp] theorem area_self (u : List Bool) : area u u = 0 := by
  induction u with
  | nil => rfl
  | cons a u ih => simp [area, ih]

/-- The transport area obeys the triangle inequality at a fixed word length. -/
theorem area_triangle (u v w : List Bool)
    (huv : u.length = v.length) (hvw : v.length = w.length) :
    area u w ≤ area u v + area v w := by
  induction u generalizing v w with
  | nil =>
    cases v with
    | nil => simp [area]
    | cons b v => simp only [List.length_nil, List.length_cons] at huv; omega
  | cons a u ih =>
    cases v with
    | nil => simp at huv
    | cons b v =>
      cases w with
      | nil => simp at hvw
      | cons c w =>
        have h := ih v w (by simpa using huv) (by simpa using hvw)
        have ht := abs_add_le ((u.count true : ℤ) - (v.count true : ℤ))
          ((v.count true : ℤ) - (w.count true : ℤ))
        have he : ((u.count true : ℤ) - (v.count true : ℤ)) +
            ((v.count true : ℤ) - (w.count true : ℤ)) =
            ((u.count true : ℤ) - (w.count true : ℤ)) := by ring
        rw [he] at ht
        simp only [area]
        omega

/-- Every actual swap derivation has at least the suffix transport area steps. -/
theorem area_le_swaps {n u v} (h : Swaps n u v) : area u v ≤ (n : ℤ) := by
  induction h with
  | refl w => simp
  | swap a b w hab =>
    cases a <;> cases b <;> simp_all [area]
  | @cons a n u v h ih =>
    have hc := List.perm_iff_count.mp h.perm true
    simp only [area, hc, sub_self, abs_zero, zero_add]
    exact ih
  | @trans m n u v w h₁ h₂ ih₁ ih₂ =>
    have ht := area_triangle u v w h₁.perm.length_eq h₂.perm.length_eq
    push_cast
    omega

/-- The minimum number of swaps exists, with a witnessed derivation and the
proved area lower bound. Equality with area is deliberately not asserted. -/
theorem minimum_swaps_exists {u v : List Bool}
    (hlen : u.length = v.length) (hc : charge u = charge v) :
    ∃ n, Swaps n u v ∧ (∀ m, Swaps m u v → n ≤ m) ∧ area u v ≤ (n : ℤ) := by
  classical
  have hex := equal_total_reachable hlen hc
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_, area_le_swaps (Nat.find_spec hex)⟩
  intro m hm
  exact Nat.find_min' hex hm

#print axioms paired_even_prefix
#print axioms paired_odd_prefix
#print axioms area_le_swaps
#print axioms minimum_swaps_exists
#print axioms equal_total_reachable
#print axioms reaches_paired
#print axioms reaches_alternatingOdd
end ColorTransport
