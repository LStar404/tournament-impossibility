import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Factorial.Basic

namespace NonAlgebraicity

/-- Redundant but finite encoding: only the entries i < j are used. -/
abbrev Orientation (n : ℕ) := Fin n → Fin n → Bool

/-- Orient every unordered pair exactly once, with no loops. -/
def edge {n : ℕ} (o : Orientation n) (i j : Fin n) : Bool :=
  if i < j then o i j else if j < i then !(o j i) else false

@[simp] theorem edge_irrefl {n : ℕ} (o : Orientation n) (i : Fin n) :
    edge o i i = false := by simp [edge]

theorem edge_opposite {n : ℕ} (o : Orientation n) {i j : Fin n} (h : i ≠ j) :
    edge o i j = !(edge o j i) := by
  rcases lt_or_gt_of_ne h with hij | hji
  · simp [edge, hij, not_lt_of_ge hij.le]
  · simp [edge, hji, not_lt_of_ge hji.le]

/-- Every loop-free tournament relation occurs in the finite encoding. -/
theorem represents_every_tournament {n : ℕ} (r : Fin n → Fin n → Bool)
    (hd : ∀ i, r i i = false)
    (ho : ∀ i j, i ≠ j → r i j = !(r j i)) :
    ∃ o : Orientation n, ∀ i j, edge o i j = r i j := by
  refine ⟨r, ?_⟩
  intro i j
  rcases lt_trichotomy i j with h | h | h
  · simp [edge, h]
  · subst j; simp [edge, hd]
  · simp [edge, h, not_lt_of_ge h.le, ho i j (ne_of_gt h)]

/-- A permutation represents its ordered list of vertices. -/
def IsHamiltonianOrder {n : ℕ} (o : Orientation n) (p : Equiv.Perm (Fin n)) : Prop :=
  ∀ i j : Fin n, j.val = i.val + 1 → edge o (p i) (p j) = true

noncomputable def hamiltonianPathCount {n : ℕ} (o : Orientation n) : ℕ := by
  classical
  exact (Finset.univ.filter (IsHamiltonianOrder o)).card

/-- Exact finite maximum. Redundant bits do not affect the supremum. -/
noncomputable def maximalPathCount (n : ℕ) : ℕ := by
  classical
  exact Finset.univ.sup (fun o : Orientation n => hamiltonianPathCount o)

theorem pathCount_le_maximal {n : ℕ} (o : Orientation n) :
    hamiltonianPathCount o ≤ maximalPathCount n := by
  classical
  exact Finset.le_sup (f := fun o : Orientation n => hamiltonianPathCount o) (Finset.mem_univ o)

/-- The paper starts at n = 1, so the constant term is set to zero. -/
noncomputable def normalizedCoefficient (n : ℕ) : ℚ :=
  if n = 0 then 0 else
    (2 : ℚ) ^ (n - 1) * (maximalPathCount n : ℚ) / (n.factorial : ℚ)

@[simp] theorem normalizedCoefficient_zero : normalizedCoefficient 0 = 0 := by
  simp [normalizedCoefficient]

#print axioms pathCount_le_maximal
end NonAlgebraicity
