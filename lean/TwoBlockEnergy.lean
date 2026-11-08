import Mathlib

noncomputable section
namespace TwoBlockEnergy
open Finset Matrix
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def ones (ι : Type*) : ι → ℝ := fun _ => 1

def first (A : Matrix ι ι ℝ) : ℝ := ∑ i, (A.mulVec (ones ι) i)^2

def second (A : Matrix ι ι ℝ) : ℝ :=
  ∑ i, (A.mulVec (A.mulVec (ones ι)) i)^2

def join (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ) : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ :=
  fromBlocks A (fun _ _ => 1) (fun _ _ => -1) B

lemma skew_pair (A : Matrix ι ι ℝ) (hA : ∀ i j, A i j = -A j i)
    (x y : ι → ℝ) : dotProduct x (A.mulVec y) = -dotProduct y (A.mulVec x) := by
  simp only [dotProduct, mulVec, mul_sum, ← sum_neg_distrib]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  rw [hA j i]
  ring

lemma skew_self (A : Matrix ι ι ℝ) (hA : ∀ i j, A i j = -A j i)
    (x : ι → ℝ) : dotProduct x (A.mulVec x) = 0 := by
  have h := skew_pair A hA x x
  linarith

lemma sum_action (A : Matrix ι ι ℝ) (hA : ∀ i j, A i j = -A j i) :
    ∑ i, A.mulVec (ones ι) i = 0 := by
  simpa [dotProduct, ones] using skew_self A hA (ones ι)

lemma sum_second_action (A : Matrix ι ι ℝ) (hA : ∀ i j, A i j = -A j i) :
    ∑ i, A.mulVec (A.mulVec (ones ι)) i = -first A := by
  simpa [dotProduct, ones, first, pow_two] using skew_pair A hA (ones ι) (A.mulVec (ones ι))

lemma action_cross (A : Matrix ι ι ℝ) (hA : ∀ i j, A i j = -A j i) :
    ∑ i, A.mulVec (A.mulVec (ones ι)) i * A.mulVec (ones ι) i = 0 := by
  simpa [dotProduct, mul_comm] using skew_self A hA (A.mulVec (ones ι))

lemma square_shift (x : ι → ℝ) (c : ℝ) (hx : ∑ i, x i = 0) :
    (∑ i, (x i+c)^2) = (∑ i, (x i)^2)+(Fintype.card ι : ℝ)*c^2 := by
  calc
    _ = ∑ i, ((x i)^2+2*c*x i+c^2) := by apply sum_congr rfl; intro i hi; ring
    _ = _ := by simp [sum_add_distrib, ← mul_sum, hx]

lemma square_second_shift (A : Matrix ι ι ℝ)
    (hA : ∀ i j, A i j = -A j i) (c d : ℝ) :
    (∑ i, (A.mulVec (A.mulVec (ones ι)) i+c*A.mulVec (ones ι) i+d)^2) =
      second A+(c^2-2*d)*first A+(Fintype.card ι : ℝ)*d^2 := by
  calc
    _ = ∑ i, ((A.mulVec (A.mulVec (ones ι)) i)^2+
        c^2*(A.mulVec (ones ι) i)^2+d^2+
        2*c*(A.mulVec (A.mulVec (ones ι)) i*A.mulVec (ones ι) i)+
        2*d*A.mulVec (A.mulVec (ones ι)) i+2*c*d*A.mulVec (ones ι) i) := by
      apply sum_congr rfl; intro i hi; ring
    _ = _ := by
      simp only [sum_add_distrib, ← mul_sum, action_cross A hA,
        sum_second_action A hA, sum_action A hA, mul_zero, add_zero,
        sum_const, card_univ, nsmul_eq_mul]
      unfold second first
      ring

lemma join_action_left (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ) (i : ι) :
    (join A B).mulVec (ones (ι ⊕ κ)) (Sum.inl i) =
      A.mulVec (ones ι) i+(Fintype.card κ : ℝ) := by
  simp [join, fromBlocks, mulVec, dotProduct, ones, Fintype.sum_sum_type]

lemma join_action_right (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ) (i : κ) :
    (join A B).mulVec (ones (ι ⊕ κ)) (Sum.inr i) =
      B.mulVec (ones κ) i-(Fintype.card ι : ℝ) := by
  simp [join, fromBlocks, mulVec, dotProduct, ones, Fintype.sum_sum_type]
  ring

lemma join_second_left (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ)
    (hB : ∀ i j, B i j = -B j i) (i : ι) :
    (join A B).mulVec ((join A B).mulVec (ones (ι ⊕ κ))) (Sum.inl i) =
      A.mulVec (A.mulVec (ones ι)) i+(Fintype.card κ : ℝ)*A.mulVec (ones ι) i-
        (Fintype.card ι : ℝ)*(Fintype.card κ : ℝ) := by
  change (∑ j, (join A B) (Sum.inl i) j * ((join A B).mulVec (ones (ι ⊕ κ)) j)) = _
  rw [Fintype.sum_sum_type]
  change (∑ j, A i j * ((join A B).mulVec (ones (ι ⊕ κ)) (Sum.inl j)))+
    (∑ j, 1 * ((join A B).mulVec (ones (ι ⊕ κ)) (Sum.inr j))) = _
  simp only [join_action_left, join_action_right, one_mul, mul_add,
    sum_add_distrib, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul,
    ← sum_mul, sum_action B hB]
  simp only [mulVec, dotProduct, ones, mul_one]
  ring

lemma join_second_right (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ)
    (hA : ∀ i j, A i j = -A j i) (i : κ) :
    (join A B).mulVec ((join A B).mulVec (ones (ι ⊕ κ))) (Sum.inr i) =
      B.mulVec (B.mulVec (ones κ)) i-(Fintype.card ι : ℝ)*B.mulVec (ones κ) i-
        (Fintype.card ι : ℝ)*(Fintype.card κ : ℝ) := by
  change (∑ j, (join A B) (Sum.inr i) j * ((join A B).mulVec (ones (ι ⊕ κ)) j)) = _
  rw [Fintype.sum_sum_type]
  change (∑ j, (-1) * ((join A B).mulVec (ones (ι ⊕ κ)) (Sum.inl j)))+
    (∑ j, B i j * ((join A B).mulVec (ones (ι ⊕ κ)) (Sum.inr j))) = _
  simp only [join_action_left, join_action_right, mul_add, mul_sub,
    sum_add_distrib, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul,
    ← sum_mul, ← mul_sum, sum_action A hA]
  simp only [mulVec, dotProduct, ones, mul_one]
  ring

 theorem first_join (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ)
    (hA : ∀ i j, A i j = -A j i) (hB : ∀ i j, B i j = -B j i) :
    first (join A B) = first A+first B+
      (Fintype.card ι : ℝ)*(Fintype.card κ : ℝ)*
        ((Fintype.card ι : ℝ)+(Fintype.card κ : ℝ)) := by
  unfold first
  rw [Fintype.sum_sum_type]
  simp only [join_action_left, join_action_right, sub_eq_add_neg]
  rw [square_shift _ _ (sum_action A hA), square_shift _ _ (sum_action B hB)]
  ring

 theorem second_join (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ)
    (hA : ∀ i j, A i j = -A j i) (hB : ∀ i j, B i j = -B j i) :
    second (join A B) = second A+second B+
      ((Fintype.card κ : ℝ)^2+2*(Fintype.card ι : ℝ)*(Fintype.card κ : ℝ))*first A+
      ((Fintype.card ι : ℝ)^2+2*(Fintype.card ι : ℝ)*(Fintype.card κ : ℝ))*first B+
      (Fintype.card ι : ℝ)^2*(Fintype.card κ : ℝ)^2*
        ((Fintype.card ι : ℝ)+(Fintype.card κ : ℝ)) := by
  unfold second at ⊢
  rw [Fintype.sum_sum_type]
  simp only [join_second_left A B hB, join_second_right A B hA, sub_eq_add_neg,
    ← neg_mul]
  rw [square_second_shift A hA, square_second_shift B hB]
  unfold second
  ring
end TwoBlockEnergy
#print axioms TwoBlockEnergy.first_join
#print axioms TwoBlockEnergy.second_join
