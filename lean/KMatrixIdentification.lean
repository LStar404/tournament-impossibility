import ReferenceSquare
import IteratedVectorMajorization
noncomputable section
namespace KMatrixIdentification
open Finset MajorizationCone ReferenceSquare IteratedVectorMajorization

/-- The explicit signed anti-diagonal matrix really is the P-difference
operator already used in the full tournament-vector theorem. -/
lemma coefficient_entry (n i j : ℕ) (hi : i < n) (hj : j < n) :
    pWeight n (i+1) j - pWeight n i j = Kentry n i j := by
  have hh :
      (if j < n-(i+1) then ((i+1 : ℕ) : ℤ) else ((i+1 : ℕ) : ℤ) - (penalty (j-(n-(i+1))) : ℤ)) -
      (if j < n-i then (i : ℤ) else (i : ℤ) - (penalty (j-(n-i)) : ℤ)) =
      (if i+j < n-1 then (1:ℤ) else if i+j = n-1 then 0 else
        if (i+j-n)%2=0 then 1 else -1) := by
    unfold penalty
    split_ifs <;> push_cast <;> omega
  unfold pWeight Kentry alt
  simp only [if_pos hj]
  exact_mod_cast hh

def matrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := fun i j => Kentry n i.val j.val

lemma K_action (n : ℕ) (z : ℕ → ℝ) (i : Fin n) :
    K n z i.val = (matrix n).mulVec (fun j => z j.val) i := by
  simp only [K, if_pos i.isLt, P, Matrix.mulVec, dotProduct, matrix]
  rw [← sum_sub_distrib]
  rw [Fin.sum_univ_eq_sum_range (fun j => Kentry n i.val j * z j)]
  apply sum_congr rfl
  intro j hj
  rw [← sub_mul, coefficient_entry n i.val j i.isLt (mem_range.mp hj)]

lemma comparison_power (n : ℕ) (z : ℕ → ℝ) (r : ℕ) (i : Fin n) :
    comparison n z r i.val = (matrix n ^ r).mulVec (fun j => z j.val) i := by
  induction r generalizing i with
  | zero => simp [comparison]
  | succ r ih =>
    rw [comparison, K_action]
    have he : (fun j : Fin n => comparison n z r j.val) =
        (matrix n ^ r).mulVec (fun j => z j.val) := by
      funext j
      exact ih j
    rw [he, Matrix.mulVec_mulVec, ← pow_succ']
end KMatrixIdentification
#print axioms KMatrixIdentification.coefficient_entry
#print axioms KMatrixIdentification.comparison_power
