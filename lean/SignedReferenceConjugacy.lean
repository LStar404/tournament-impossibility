import ReferenceDiagonal
import ZigzagReference
noncomputable section
namespace SignedReferenceConjugacy
open Finset ReferenceSquare ReferenceDiagonal ZigzagReference

lemma K_square_symmetric (n : ℕ) (i j : Fin n) :
    (Kmatrix n ^ 2) i j = (Kmatrix n ^ 2) j i := by
  rw [K_square_entry, K_square_entry]
  apply sum_congr rfl; intro l hl; ring

lemma neg_T_square_symmetric (n : ℕ) (i j : Fin n) :
    (-(Tmatrix n ^ 2)) i j = (-(Tmatrix n ^ 2)) j i := by
  rw [neg_T_square_formula, neg_T_square_formula]
  by_cases h : i=j
  · subst j; rfl
  · simp only [if_neg h, if_neg (Ne.symm h), abs_sub_comm]

lemma concrete_entry_lt (n : ℕ) (i j : Fin n) (hij : i < j) :
    (Kmatrix n ^ 2) i j = sigma i.val * sigma j.val *
      (-(Tmatrix n ^ 2)) (perm n i) (perm n j) := by
  have hp : perm n i ≠ perm n j := (perm n).injective.ne (ne_of_lt hij)
  rw [K_square_entry, K_row_dot_offdiag n i.val j.val hij j.isLt,
    neg_T_square_formula]
  simp only [if_neg hp]
  exact conjugacy_arithmetic n i.val j.val hij j.isLt

/-- Concrete signed-permutation reference-square identity for every n.
No reference identity is included among its hypotheses. -/
theorem concrete_entry (n : ℕ) (i j : Fin n) :
    (Kmatrix n ^ 2) i j = sigma i.val * sigma j.val *
      (-(Tmatrix n ^ 2)) (perm n i) (perm n j) := by
  rcases lt_trichotomy i j with h | h | h
  · exact concrete_entry_lt n i j h
  · subst j
    rw [K_square_entry, K_row_dot_diag n i.val i.isLt, neg_T_square_formula]
    simp only [ite_true, sigma_sq, one_mul]
  · rw [K_square_symmetric, concrete_entry_lt n j i h,
      neg_T_square_symmetric n (perm n j) (perm n i)]
    ring

/-- The actual signed permutation matrix, Qx(i)=sigma(i)*x(perm(i)). -/
def Q (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if j = perm n i then sigma i.val else 0

lemma Q_conjugate_entry (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (Q n * A * (Q n).transpose) i j =
      sigma i.val * sigma j.val * A (perm n i) (perm n j) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Q]
  have hfirst (b : Fin n) :
      (∑ a : Fin n, (if a = perm n i then sigma i.val else 0) * A a b) =
      sigma i.val * A (perm n i) b := by
    rw [sum_eq_single (perm n i)]
    · simp
    · intro a ha hne; simp [hne]
    · simp
  simp_rw [hfirst]
  rw [sum_eq_single (perm n j)]
  · simp; ring
  · intro a ha hne; simp [hne]
  · simp

/-- Q really is orthogonal, not merely a notation for an entry formula. -/
theorem Q_orthogonal (n : ℕ) : Q n * (Q n).transpose = 1 := by
  ext i j
  have he := Q_conjugate_entry n 1 i j
  rw [Matrix.mul_one] at he
  rw [he]
  by_cases hij : i=j
  · subst j; simp [Matrix.one_apply, sigma_sq]
  · have hp : perm n i ≠ perm n j := (perm n).injective.ne hij
    simp [Matrix.one_apply, hij, hp]

/-- Full explicit matrix equality K²=Q(-T²)Qᵀ. -/
theorem concrete_square_conjugacy (n : ℕ) :
    Kmatrix n ^ 2 = Q n * (-(Tmatrix n ^ 2)) * (Q n).transpose := by
  ext i j
  rw [Q_conjugate_entry]
  exact concrete_entry n i j
end SignedReferenceConjugacy
#print axioms SignedReferenceConjugacy.concrete_entry
#print axioms SignedReferenceConjugacy.concrete_square_conjugacy

#print axioms SignedReferenceConjugacy.Q_orthogonal
