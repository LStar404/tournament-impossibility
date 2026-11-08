import TwoBlockEnergy
import OrdinalMomentRecurrence
noncomputable section
namespace OrdinalBlockMatrix
open Finset Matrix

def Carrier (m : ℕ → ℕ) : ℕ → Type
  | 0 => Fin 0
  | k+1 => Carrier m k ⊕ Fin (m k)

instance carrierFintype (m : ℕ → ℕ) (k : ℕ) : Fintype (Carrier m k) := by
  induction k with
  | zero => exact inferInstanceAs (Fintype (Fin 0))
  | succ k ih =>
    letI := ih
    exact inferInstanceAs (Fintype (Carrier m k ⊕ Fin (m k)))

instance carrierDecidableEq (m : ℕ → ℕ) (k : ℕ) : DecidableEq (Carrier m k) := by
  induction k with
  | zero => exact inferInstanceAs (DecidableEq (Fin 0))
  | succ k ih =>
    letI := ih
    exact inferInstanceAs (DecidableEq (Carrier m k ⊕ Fin (m k)))

/-- Actual ordered block matrix, on a nested finite sum of its block indices. -/
def matrix (m : ℕ → ℕ) (A : ∀ i, Matrix (Fin (m i)) (Fin (m i)) ℝ) :
    (k : ℕ) → Matrix (Carrier m k) (Carrier m k) ℝ
  | 0 => 0
  | k+1 => TwoBlockEnergy.join (matrix m A k) (A k)

lemma cardinality (m : ℕ → ℕ) (k : ℕ) :
    Fintype.card (Carrier m k) = ∑ i ∈ range k, m i := by
  induction k with
  | zero => exact Fintype.card_fin 0
  | succ k ih =>
    change Fintype.card (Carrier m k ⊕ Fin (m k)) = _
    rw [Fintype.card_sum, Fintype.card_fin, sum_range_succ, ih]

lemma skew (m : ℕ → ℕ) (A : ∀ i, Matrix (Fin (m i)) (Fin (m i)) ℝ)
    (hA : ∀ k i j, A k i j = -A k j i) (k : ℕ) :
    ∀ i j, matrix m A k i j = -matrix m A k j i := by
  induction k with
  | zero => intro i; exact Fin.elim0 i
  | succ k ih =>
    intro i j
    cases i with
    | inl i =>
      cases j with
      | inl j => exact ih i j
      | inr j => norm_num [matrix, TwoBlockEnergy.join, Matrix.fromBlocks]
    | inr i =>
      cases j with
      | inl j => norm_num [matrix, TwoBlockEnergy.join, Matrix.fromBlocks]
      | inr j => exact hA k i j

def packet (m : ℕ → ℕ) (A : ∀ i, Matrix (Fin (m i)) (Fin (m i)) ℝ)
    (i : ℕ) : OrdinalMomentRecurrence.Packet where
  size := m i
  first := TwoBlockEnergy.first (A i)
  second := TwoBlockEnergy.second (A i)
  sixth := ∑ x, ∑ y, (((A i)^3) x y)^2

lemma packet_cumulative_size (m : ℕ → ℕ)
    (A : ∀ i, Matrix (Fin (m i)) (Fin (m i)) ℝ) (k : ℕ) :
    (OrdinalMomentRecurrence.cumulative (packet m A) k).size =
      (Fintype.card (Carrier m k) : ℝ) := by
  rw [OrdinalMomentRecurrence.cumulative_size, cardinality]
  simp [packet, Nat.cast_sum]

/-- Actual source energies of the recursively constructed ordered block matrix
agree with the first two fields of the polynomial recurrence. -/
theorem source_energies (m : ℕ → ℕ)
    (A : ∀ i, Matrix (Fin (m i)) (Fin (m i)) ℝ)
    (hA : ∀ k i j, A k i j = -A k j i) (k : ℕ) :
    TwoBlockEnergy.first (matrix m A k) =
      (OrdinalMomentRecurrence.cumulative (packet m A) k).first ∧
    TwoBlockEnergy.second (matrix m A k) =
      (OrdinalMomentRecurrence.cumulative (packet m A) k).second := by
  induction k with
  | zero =>
    constructor <;>
      simp [matrix, Carrier, TwoBlockEnergy.first, TwoBlockEnergy.second,
        OrdinalMomentRecurrence.cumulative] <;>
      exact Finset.sum_eq_zero (fun i _ => Fin.elim0 i)
  | succ k ih =>
    change TwoBlockEnergy.first (TwoBlockEnergy.join (matrix m A k) (A k)) = _ ∧
      TwoBlockEnergy.second (TwoBlockEnergy.join (matrix m A k) (A k)) = _
    rw [TwoBlockEnergy.first_join _ _ (skew m A hA k) (hA k),
      TwoBlockEnergy.second_join _ _ (skew m A hA k) (hA k), ih.1, ih.2]
    simp only [OrdinalMomentRecurrence.cumulative, OrdinalMomentRecurrence.join,
      packet, packet_cumulative_size, Fintype.card_fin]
    trivial
end OrdinalBlockMatrix
