import Mathlib
noncomputable section
namespace ReferenceSquare
open Finset

def alt (r : ℕ) : ℝ := if r % 2 = 0 then 1 else -1

def Kentry (n i j : ℕ) : ℝ :=
  if i+j < n-1 then 1 else if i+j = n-1 then 0 else alt (i+j-n)

def Tentry (i j : ℕ) : ℝ := if i < j then 1 else if j < i then -1 else 0

lemma alt_sq (r : ℕ) : alt r * alt r = 1 := by
  unfold alt; split_ifs <;> norm_num
lemma alt_add (a b : ℕ) : alt (a+b) = alt a * alt b := by
  unfold alt
  have ha := Nat.mod_lt a (by omega : 0 < 2)
  have hb := Nat.mod_lt b (by omega : 0 < 2)
  rw [Nat.add_mod]
  split_ifs <;> norm_num at * <;> omega

lemma sum_alt (r : ℕ) : (∑ j ∈ range r, alt j) = if r % 2 = 0 then 0 else 1 := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [sum_range_succ, ih]
    unfold alt
    have hm := Nat.mod_lt r (by omega : 0 < 2)
    rw [Nat.add_mod]
    split_ifs <;> norm_num at * <;> omega

lemma sum_split (f : ℕ → ℝ) (n a : ℕ) (ha : a ≤ n) :
    (∑ j ∈ range n, f j) = (∑ j ∈ range a, f j) +
      ∑ j ∈ range (n-a), f (a+j) := by
  have h := sum_range_add f a (n-a)
  have he : a+(n-a) = n := by omega
  rw [he] at h
  exact h

/-- Exact finite decomposition at two exceptional coordinates. -/
lemma sum_two_breaks (f : ℕ → ℝ) (n a b : ℕ) (hab : a < b) (hb : b < n) :
    (∑ j ∈ range n, f j) =
      (∑ j ∈ range a, f j) + f a +
      (∑ j ∈ range (b-a-1), f (a+1+j)) + f b +
      ∑ j ∈ range (n-b-1), f (b+1+j) := by
  rw [sum_split f n (b+1) (by omega), sum_range_succ,
    sum_split f b (a+1) (by omega), sum_range_succ]
  have he : b-(a+1) = b-a-1 := by omega
  have he' : n-(b+1) = n-b-1 := by omega
  rw [he, he']

lemma T_skew (i j : ℕ) : Tentry i j = -Tentry j i := by
  unfold Tentry
  split_ifs <;> norm_num <;> omega

lemma T_diagonal (i : ℕ) : Tentry i i = 0 := by simp [Tentry]

/-- The exact row inner product of the transitive sign matrix. -/
theorem T_row_dot_offdiag (n i j : ℕ) (hij : i < j) (hj : j < n) :
    (∑ l ∈ range n, Tentry i l * Tentry j l) = (n : ℝ) - 2*(j-i : ℕ) := by
  rw [sum_two_breaks (fun l => Tentry i l * Tentry j l) n i j hij hj]
  have ha : (∑ l ∈ range i, Tentry i l * Tentry j l) = (i : ℝ) := by
    calc
      _ = ∑ l ∈ range i, (1 : ℝ) := by
        apply sum_congr rfl; intro l hl
        have hl' := mem_range.mp hl
        simp [Tentry, show ¬ i < l by omega, show l < i by omega,
          show ¬ j < l by omega, show l < j by omega]
      _ = _ := by simp
  have hm : (∑ l ∈ range (j-i-1), Tentry i (i+1+l) * Tentry j (i+1+l)) =
      -((j-i-1 : ℕ) : ℝ) := by
    calc
      _ = ∑ l ∈ range (j-i-1), (-1 : ℝ) := by
        apply sum_congr rfl; intro l hl
        have hl' := mem_range.mp hl
        simp [Tentry, show i < i+1+l by omega, show ¬ j < i+1+l by omega,
          show i+1+l < j by omega]
      _ = _ := by simp
  have hb : (∑ l ∈ range (n-j-1), Tentry i (j+1+l) * Tentry j (j+1+l)) =
      ((n-j-1 : ℕ) : ℝ) := by
    calc
      _ = ∑ l ∈ range (n-j-1), (1 : ℝ) := by
        apply sum_congr rfl; intro l hl
        simp [Tentry, show i < j+1+l by omega, show j < j+1+l by omega]
      _ = _ := by simp
  rw [ha, hm, hb, T_diagonal, T_diagonal]
  have h : (i : ℤ) - (j-i-1 : ℕ) + (n-j-1 : ℕ) = (n : ℤ) - 2*(j-i : ℕ) := by omega
  have hh : (i : ℝ) - ((j-i-1 : ℕ) : ℝ) + ((n-j-1 : ℕ) : ℝ) =
      (n : ℝ) - 2*((j-i : ℕ) : ℝ) := by exact_mod_cast h
  norm_num
  linarith


lemma K_symm (n i j : ℕ) : Kentry n i j = Kentry n j i := by
  simp [Kentry, Nat.add_comm]
lemma K_break (n i : ℕ) (hi : i < n) : Kentry n i (n-1-i) = 0 := by
  have h : i+(n-1-i) = n-1 := by omega
  simp [Kentry, h]

/-- Three nonzero blocks of the K row inner product, proved for arbitrary N. -/
theorem K_row_dot_offdiag (n i j : ℕ) (hij : i < j) (hj : j < n) :
    (∑ l ∈ range n, Kentry n i l * Kentry n j l) =
      ((n-1-j : ℕ) : ℝ) + (if (j-i-1) % 2 = 0 then 0 else 1) +
      (i : ℝ) * alt (j-i) := by
  have hi : i < n := by omega
  let a := n-1-j
  let b := n-1-i
  have hab : a < b := by dsimp [a,b]; omega
  have hbn : b < n := by dsimp [b]; omega
  rw [sum_two_breaks (fun l => Kentry n i l * Kentry n j l) n a b hab hbn]
  have ha : (∑ l ∈ range a, Kentry n i l * Kentry n j l) = (a : ℝ) := by
    calc
      _ = ∑ l ∈ range a, (1 : ℝ) := by
        apply sum_congr rfl; intro l hl
        have hl' := mem_range.mp hl
        simp [Kentry, show i+l < n-1 by dsimp [a] at hl'; omega,
          show j+l < n-1 by dsimp [a] at hl'; omega]
      _ = _ := by simp
  have hm : (∑ l ∈ range (b-a-1), Kentry n i (a+1+l) * Kentry n j (a+1+l)) =
      if (j-i-1) % 2 = 0 then 0 else 1 := by
    have hlen : b-a-1 = j-i-1 := by dsimp [a,b]; omega
    rw [hlen]
    calc
      _ = ∑ l ∈ range (j-i-1), alt l := by
        apply sum_congr rfl; intro l hl
        have hl' := mem_range.mp hl
        have h1 : i+(a+1+l) < n-1 := by dsimp [a]; omega
        have h2 : ¬ j+(a+1+l) < n-1 := by dsimp [a]; omega
        have h3 : ¬ j+(a+1+l) = n-1 := by dsimp [a]; omega
        have h4 : j+(a+1+l)-n = l := by dsimp [a]; omega
        simp [Kentry, h1, h2, h3, h4]
      _ = _ := sum_alt _
  have hb : (∑ l ∈ range (n-b-1), Kentry n i (b+1+l) * Kentry n j (b+1+l)) =
      (i : ℝ) * alt (j-i) := by
    have hlen : n-b-1 = i := by dsimp [b]; omega
    rw [hlen]
    calc
      _ = ∑ l ∈ range i, alt (j-i) := by
        apply sum_congr rfl; intro l hl
        have h1 : ¬ i+(b+1+l) < n-1 := by dsimp [b]; omega
        have h2 : ¬ i+(b+1+l) = n-1 := by dsimp [b]; omega
        have h3 : ¬ j+(b+1+l) < n-1 := by dsimp [b]; omega
        have h4 : ¬ j+(b+1+l) = n-1 := by dsimp [b]; omega
        have h5 : i+(b+1+l)-n = l := by dsimp [b]; omega
        have h6 : j+(b+1+l)-n = (j-i)+l := by dsimp [b]; omega
        simp only [Kentry, if_neg h1, if_neg h2, if_neg h3, if_neg h4, h5, h6]
        rw [alt_add]
        calc
          _ = alt (j-i) * (alt l * alt l) := by ring
          _ = _ := by rw [alt_sq, mul_one]
      _ = _ := by simp
  have hza : Kentry n j a = 0 := K_break n j hj
  have hzb : Kentry n i b = 0 := K_break n i hi
  rw [ha, hm, hb, hza, hzb]
  dsimp [a]
  ring

end ReferenceSquare
#print axioms ReferenceSquare.T_row_dot_offdiag

#print axioms ReferenceSquare.K_row_dot_offdiag
