import OrdinalBlockMatrix
import TwoBlockSixthMoment
import TransitiveOrbit
noncomputable section
namespace OrdinalTransitiveReference
open Finset Matrix OrdinalBlockMatrix TransitiveOrbit

def total (m : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => total m k + m k

lemma total_eq_sum (m : ℕ → ℕ) (k : ℕ) : total m k = ∑ i ∈ range k, m i := by
  induction k with
  | zero => simp [total]
  | succ k ih => simp [total, sum_range_succ, ih]

/-- The natural block-order concatenation, including empty blocks. -/
def blockEquiv (m : ℕ → ℕ) : (k : ℕ) → Carrier m k ≃ Fin (total m k)
  | 0 => Equiv.refl _
  | k+1 => (Equiv.sumCongr (blockEquiv m k) (Equiv.refl _)).trans finSumFinEquiv

@[simp] lemma blockEquiv_inl (m : ℕ → ℕ) (k : ℕ) (i : Carrier m k) :
    blockEquiv m (k+1) (Sum.inl i) = Fin.castAdd (m k) (blockEquiv m k i) := rfl
@[simp] lemma blockEquiv_inr (m : ℕ → ℕ) (k : ℕ) (i : Fin (m k)) :
    blockEquiv m (k+1) (Sum.inr i) = Fin.natAdd (total m k) i := rfl

/-- Joining actual transitive blocks gives exactly the transitive matrix in
natural block order; the entry identity is proved, not assumed. -/
theorem entry (m : ℕ → ℕ) (k : ℕ) (i j : Carrier m k) :
    matrix m (fun a => T (m a)) k i j =
      T (total m k) (blockEquiv m k i) (blockEquiv m k j) := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        change matrix m (fun a => T (m a)) k i j =
          T (total m k + m k) (Fin.castAdd (m k) (blockEquiv m k i))
            (Fin.castAdd (m k) (blockEquiv m k j))
        rw [ih i j]
        rfl
      | inr j =>
        change (1 : ℝ) = T (total m k + m k)
          (Fin.castAdd (m k) (blockEquiv m k i)) (Fin.natAdd (total m k) j)
        have hi := (blockEquiv m k i).isLt
        simp [T, Fin.lt_def, show (blockEquiv m k i).val < total m k + j.val by omega]
    | inr i =>
      cases j with
      | inl j =>
        change (-1 : ℝ) = T (total m k + m k)
          (Fin.natAdd (total m k) i) (Fin.castAdd (m k) (blockEquiv m k j))
        have hj := (blockEquiv m k j).isLt
        simp [T, Fin.lt_def, show ¬total m k + i.val < (blockEquiv m k j).val by omega,
          show (blockEquiv m k j).val < total m k + i.val by omega]
      | inr j =>
        change T (m k) i j = T (total m k + m k)
          (Fin.natAdd (total m k) i) (Fin.natAdd (total m k) j)
        simp only [T, Fin.lt_def, Fin.val_natAdd, Nat.add_lt_add_iff_left]

section Relabeling
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

lemma power_entry (e : ι ≃ κ) (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ)
    (h : ∀ i j, A i j = B (e i) (e j)) (r : ℕ) (i j : ι) :
    (A^r) i j = (B^r) (e i) (e j) := by
  induction r generalizing i j with
  | zero => simp [Matrix.one_apply]
  | succ r ih =>
    simp only [pow_succ, Matrix.mul_apply]
    have he : (∑ k : ι, (A^r) i k * A k j) =
        ∑ k : ι, (B^r) (e i) (e k) * B (e k) (e j) := by
      apply sum_congr rfl
      intro k hk
      rw [ih, h]
    rw [he]
    exact Equiv.sum_comp e (fun k => (B^r) (e i) k * B k (e j))

lemma power_frobenius_relabel (e : ι ≃ κ) (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ)
    (h : ∀ i j, A i j = B (e i) (e j)) (r : ℕ) :
    (∑ i : ι, ∑ j : ι, ((A^r) i j)^2) =
      ∑ i : κ, ∑ j : κ, ((B^r) i j)^2 := by
  calc
    _ = ∑ i : ι, ∑ j : ι, ((B^r) (e i) (e j))^2 := by
      apply sum_congr rfl; intro i hi
      apply sum_congr rfl; intro j hj
      rw [power_entry e A B h r i j]
    _ = ∑ i : ι, ∑ j : κ, ((B^r) (e i) j)^2 := by
      apply sum_congr rfl; intro i hi
      exact Equiv.sum_comp e (fun j => ((B^r) (e i) j)^2)
    _ = _ := Equiv.sum_comp e (fun i => ∑ j : κ, ((B^r) i j)^2)
end Relabeling

/-- Every natural-number-power Frobenius moment of the actual ordered transitive-block join
is that of the single transitive matrix of the total size. -/
theorem power_frobenius_eq (m : ℕ → ℕ) (k r : ℕ) :
    (∑ i : Carrier m k, ∑ j : Carrier m k,
      (((matrix m (fun a => T (m a)) k)^r) i j)^2) =
      ∑ i : Fin (∑ a ∈ range k, m a), ∑ j : Fin (∑ a ∈ range k, m a),
        (((T (∑ a ∈ range k, m a))^r) i j)^2 := by
  have h := power_frobenius_relabel (blockEquiv m k)
    (matrix m (fun a => T (m a)) k) (T (total m k)) (entry m k) r
  calc
    _ = ∑ i : Fin (total m k), ∑ j : Fin (total m k),
        (((T (total m k))^r) i j)^2 := h
    _ = _ := congrArg (fun q : ℕ => ∑ i : Fin q, ∑ j : Fin q, (((T q)^r) i j)^2)
      (total_eq_sum m k)

/-- The sixth reference moment, in the exact API used by the ordinal bridge. -/
theorem sixth_eq (m : ℕ → ℕ) (k : ℕ) :
    TwoBlockSixthMoment.third (matrix m (fun a => T (m a)) k) =
      TwoBlockSixthMoment.third (T (∑ a ∈ range k, m a)) := by
  simpa only [TwoBlockSixthMoment.third, RectangularFrobenius.sqnorm,
    RectangularFrobenius.inner, pow_two] using power_frobenius_eq m k 3
end OrdinalTransitiveReference
#print axioms OrdinalTransitiveReference.entry
#print axioms OrdinalTransitiveReference.power_frobenius_eq
#print axioms OrdinalTransitiveReference.sixth_eq
