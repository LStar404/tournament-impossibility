import ReferenceSquare
noncomputable section
namespace ZigzagReference
open Finset ReferenceSquare

def position (n i : ℕ) : ℕ :=
  if i = 0 then 0 else if i % 2 = 1 then (i+1)/2 else n-i/2

def sigma (i : ℕ) : ℝ := if i = 0 ∨ i % 2 = 1 then 1 else -1

lemma position_lt (n i : ℕ) (hi : i < n) : position n i < n := by
  unfold position
  split_ifs <;> omega
lemma position_inj (n i j : ℕ) (hi : i < n) (hj : j < n)
    (h : position n i = position n j) : i = j := by
  unfold position at h
  split_ifs at h <;> omega

def perm (n : ℕ) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective (fun i : Fin n => (⟨position n i.val, position_lt n i.val i.isLt⟩ : Fin n))
    (by
      have hi : Function.Injective (fun i : Fin n => (⟨position n i.val, position_lt n i.val i.isLt⟩ : Fin n)) := by
        intro i j h
        apply Fin.ext
        exact position_inj n i.val j.val i.isLt j.isLt (congrArg Fin.val h)
      exact ⟨hi, Finite.surjective_of_injective hi⟩)

lemma sigma_sq (i : ℕ) : sigma i * sigma i = 1 := by
  unfold sigma; split_ifs <;> norm_num

/-- Pure integer arithmetic behind the signed zigzag reference identity. -/
lemma conjugacy_arithmetic (n i j : ℕ) (hij : i < j) (hj : j < n) :
    ((n-1-j : ℕ) : ℝ) + (if (j-i-1) % 2 = 0 then 0 else 1) +
      (i : ℝ) * alt (j-i) =
    sigma i * sigma j * ((n : ℝ) - 2*|(position n i : ℝ)-(position n j : ℝ)|) := by
  have hh : ((n-1-j : ℕ) : ℤ) + (if (j-i-1) % 2 = 0 then 0 else 1) +
      (i : ℤ) * (if (j-i) % 2 = 0 then 1 else -1) =
    (if i = 0 ∨ i % 2 = 1 then (1:ℤ) else -1) *
    (if j = 0 ∨ j % 2 = 1 then (1:ℤ) else -1) *
    ((n : ℤ) - 2*|(position n i : ℤ)-(position n j : ℤ)|) := by
    unfold position
    split_ifs <;> simp only [one_mul, neg_one_mul, mul_one, mul_neg, neg_neg]
    all_goals first
      | (rw [abs_of_nonneg (by omega)]; omega)
      | (rw [abs_of_nonpos (by omega)]; omega)
      | omega
  unfold sigma alt
  exact_mod_cast hh
end ZigzagReference
#print axioms ZigzagReference.conjugacy_arithmetic
