import ReferenceSquare
noncomputable section
namespace ReferenceDiagonal
open Finset ReferenceSquare

lemma sum_one_except (n a : ℕ) (ha : a < n) (f : ℕ → ℝ)
    (hz : f a = 0) (ho : ∀ l < n, l ≠ a → f l = 1) :
    (∑ l ∈ range n, f l) = (n : ℝ)-1 := by
  have he : (∑ l ∈ (range n).erase a, f l) = ((n-1 : ℕ) : ℝ) := by
    calc
      _ = ∑ l ∈ (range n).erase a, (1:ℝ) := by
        apply sum_congr rfl; intro l hl
        exact ho l (mem_range.mp (mem_erase.mp hl).2) (mem_erase.mp hl).1
      _ = _ := by simp [card_erase_of_mem (mem_range.mpr ha)]
  have hs := sum_erase_add (range n) f (mem_range.mpr ha)
  rw [he, hz, add_zero] at hs
  have hnat : n-1+1 = n := by omega
  have hreal : ((n-1 : ℕ) : ℝ)+1 = (n : ℝ) := by exact_mod_cast hnat
  linarith

theorem T_row_dot_diag (n i : ℕ) (hi : i < n) :
    (∑ l ∈ range n, Tentry i l * Tentry i l) = (n : ℝ)-1 := by
  apply sum_one_except n i hi
  · simp [T_diagonal]
  · intro l hl hne
    unfold Tentry
    split_ifs <;> norm_num <;> omega

theorem K_row_dot_diag (n i : ℕ) (hi : i < n) :
    (∑ l ∈ range n, Kentry n i l * Kentry n i l) = (n : ℝ)-1 := by
  have ha : n-1-i < n := by omega
  apply sum_one_except n (n-1-i) ha
  · rw [K_break n i hi]; norm_num
  · intro l hl hne
    have hneq : i+l ≠ n-1 := by omega
    unfold Kentry
    split_ifs with hlt
    · norm_num
    · exact alt_sq _

lemma nat_distance (i j : ℕ) (hij : i ≤ j) :
    |(i : ℝ)-(j : ℝ)| = ((j-i : ℕ) : ℝ) := by
  have hreal : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
  rw [abs_of_nonpos (by linarith)]
  have hnat : j-i+i = j := by omega
  have hcast : ((j-i : ℕ) : ℝ)+(i : ℝ) = (j : ℝ) := by exact_mod_cast hnat
  linarith

/-- Unified exact transitive row-product formula, with no finite-size check. -/
theorem T_row_dot (n i j : ℕ) (hi : i < n) (hj : j < n) :
    (∑ l ∈ range n, Tentry i l * Tentry j l) =
      if i=j then (n : ℝ)-1 else (n : ℝ)-2*|(i : ℝ)-(j : ℝ)| := by
  by_cases hij : i=j
  · subst j
    simp only [ite_true]
    exact T_row_dot_diag n i hi
  · simp only [if_neg hij]
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · rw [T_row_dot_offdiag n i j hlt hj, nat_distance i j (Nat.le_of_lt hlt)]
    · have hs : (∑ l ∈ range n, Tentry i l * Tentry j l) =
          ∑ l ∈ range n, Tentry j l * Tentry i l := by
        apply sum_congr rfl; intro l hl; ring
      rw [hs, T_row_dot_offdiag n j i hgt hi, abs_sub_comm,
        nat_distance j i (Nat.le_of_lt hgt)]

def Kmatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := fun i j => Kentry n i.val j.val
def Tmatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := fun i j => Tentry i.val j.val

lemma Kmatrix_symmetric (n : ℕ) : (Kmatrix n).transpose = Kmatrix n := by
  ext i j
  exact K_symm n j.val i.val

lemma K_square_entry (n : ℕ) (i j : Fin n) :
    (Kmatrix n ^ 2) i j = ∑ l ∈ range n, Kentry n i.val l * Kentry n j.val l := by
  rw [pow_two, Matrix.mul_apply]
  have he : (∑ l : Fin n, Kmatrix n i l * Kmatrix n l j) =
      ∑ l : Fin n, Kentry n i.val l.val * Kentry n j.val l.val := by
    apply sum_congr rfl; intro l hl
    simp only [Kmatrix, K_symm n l.val j.val]
  rw [he]
  exact Fin.sum_univ_eq_sum_range (fun l => Kentry n i.val l * Kentry n j.val l) n

lemma neg_T_square_entry (n : ℕ) (i j : Fin n) :
    (-(Tmatrix n ^ 2)) i j = ∑ l ∈ range n, Tentry i.val l * Tentry j.val l := by
  simp only [Matrix.neg_apply, pow_two, Matrix.mul_apply]
  have he : (∑ l : Fin n, Tmatrix n i l * Tmatrix n l j) =
      -(∑ l : Fin n, Tentry i.val l.val * Tentry j.val l.val) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl; intro l hl
    simp only [Tmatrix, T_skew l.val j.val]
    ring
  rw [he, neg_neg]
  exact Fin.sum_univ_eq_sum_range (fun l => Tentry i.val l * Tentry j.val l) n

lemma neg_T_square_formula (n : ℕ) (i j : Fin n) :
    (-(Tmatrix n ^ 2)) i j =
      if i=j then (n : ℝ)-1 else (n : ℝ)-2*|(i.val : ℝ)-(j.val : ℝ)| := by
  rw [neg_T_square_entry, T_row_dot n i.val j.val i.isLt j.isLt]
  simp only [Fin.ext_iff]

end ReferenceDiagonal
#print axioms ReferenceDiagonal.K_row_dot_diag
#print axioms ReferenceDiagonal.T_row_dot

#print axioms ReferenceDiagonal.K_square_entry
#print axioms ReferenceDiagonal.neg_T_square_formula
