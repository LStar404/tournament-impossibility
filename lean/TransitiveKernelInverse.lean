import TournamentHamiltonian.TransitiveDeterminant
import Mathlib

noncomputable section
namespace TransitiveKernelInverse
open Matrix Finset
variable {K : Type*} [Field K] [CharZero K]

def H (n : ℕ) (a : K) : K := ((1+a)^n+(1-a)^n)/2

/-- Polynomial adjugate candidate. All natural exponents are used only in
branches where they are nonnegative. No division by a or 1±a occurs. -/
def numerator (n : ℕ) (a : K) : Matrix (Fin n) (Fin n) K := fun i j =>
  if i=j then H (n-1) a else if i < j then
    -a*(1-a)^(j.val-i.val-1)*(1+a)^(n-j.val+i.val-1)
  else a*(1+a)^(i.val-j.val-1)*(1-a)^(n-i.val+j.val-1)

lemma H_left (n : ℕ) (a : K) :
    (1-a)*H n a+a*(1+a)^n=H (n+1) a := by
  simp only [H, pow_succ]
  ring

lemma H_right (n : ℕ) (a : K) :
    a*(1-a)^n-(1+a)*H n a= -H (n+1) a := by
  simp only [H, pow_succ]
  ring

lemma kernel_entry (n : ℕ) (a : K) (i j : Fin n) :
    TournamentHamiltonian.transitiveKernel n a i j =
      if i=j then 1 else if i < j then a else -a := by
  rcases lt_trichotomy i j with h | rfl | h
  · simp [TournamentHamiltonian.transitiveKernel, TournamentHamiltonian.transitiveSkew,
      Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, h, ne_of_lt h]
  · simp [TournamentHamiltonian.transitiveKernel, TournamentHamiltonian.transitiveSkew]
  · simp [TournamentHamiltonian.transitiveKernel, TournamentHamiltonian.transitiveSkew,
      Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, h, ne_of_gt h, not_lt_of_ge h.le]

/-- A two-entry row difference, valid even at a=±1. -/
lemma kernel_row_difference (m : ℕ) (a : K) (i : Fin m) (k : Fin (m+1)) :
    TournamentHamiltonian.transitiveKernel (m+1) a i.succ k -
      TournamentHamiltonian.transitiveKernel (m+1) a i.castSucc k =
    -(1+a)*(if k=i.castSucc then 1 else 0) +
      (1-a)*(if k=i.succ then 1 else 0) := by
  simp only [kernel_entry]
  by_cases h0 : k=i.castSucc
  · subst k
    simp [Fin.castSucc_lt_succ, ne_of_gt (Fin.castSucc_lt_succ (i := i)),
      not_lt_of_ge (Fin.castSucc_lt_succ (i := i)).le,
      ne_of_lt (Fin.castSucc_lt_succ (i := i))] <;> ring
  by_cases h1 : k=i.succ
  · subst k
    simp [Fin.castSucc_lt_succ, ne_of_lt (Fin.castSucc_lt_succ (i := i)),
      ne_of_gt (Fin.castSucc_lt_succ (i := i))] <;> ring
  have hc : (i.succ < k) ↔ (i.castSucc < k) := by
    have hv0 : k.val ≠ i.val := by intro h; apply h0; exact Fin.ext h
    have hv1 : k.val ≠ i.val+1 := by intro h; apply h1; exact Fin.ext h
    simp only [Fin.lt_def, Fin.val_succ, Fin.val_castSucc]
    constructor <;> intro h <;> omega
  simp [h0, h1, Ne.symm h0, Ne.symm h1, hc]

/-- The first-plus-last boundary is sparse too; this removes geometric sums
from the inverse verification. The formula includes the one-dimensional case. -/
lemma kernel_boundary (m : ℕ) (a : K) (k : Fin (m+1)) :
    TournamentHamiltonian.transitiveKernel (m+1) a 0 k +
      TournamentHamiltonian.transitiveKernel (m+1) a (Fin.last m) k =
    (1-a)*(if k=0 then 1 else 0) +
      (1+a)*(if k=Fin.last m then 1 else 0) := by
  simp only [kernel_entry]
  by_cases h0 : k=0
  · subst k
    by_cases hm : m=0
    · subst m
      simp
    · have hh : (0 : Fin (m+1))  <  Fin.last m := by simpa only [Fin.lt_def, Fin.val_zero, Fin.val_last] using Nat.pos_of_ne_zero hm
      simp [ne_of_lt hh, ne_of_gt hh, not_lt_of_ge hh.le]
      ring
  by_cases hl : k=Fin.last m
  · subst k
    have hh : (0 : Fin (m+1))  <  Fin.last m := Fin.pos_iff_ne_zero.mpr h0
    have hm : m ≠ 0 := by intro hm; subst m; exact h0 rfl
    simp [ne_of_lt hh, hh, hm, add_comm]
  have hk0 : (0 : Fin (m+1))  <  k := Fin.pos_iff_ne_zero.mpr h0
  have hkl : k  <  Fin.last m := by
    have := k.isLt
    simp only [Fin.lt_def, Fin.val_last]
    have hk : k.val ≠ m := by intro hh; apply hl; exact Fin.ext hh
    omega
  simp [h0, hl, Ne.symm h0, Ne.symm hl, hk0, not_lt_of_ge hkl.le]

lemma numerator_row_difference (m : ℕ) (a : K) (i : Fin m) (j : Fin (m+1)) :
    (1-a)*numerator (m+1) a i.succ j -
      (1+a)*numerator (m+1) a i.castSucc j =
    H (m+1) a * ((if i.succ=j then 1 else 0) -
      (if i.castSucc=j then 1 else 0)) := by
  by_cases h0 : j=i.castSucc
  · subst j
    have he : m+1-i.succ.val+i.castSucc.val-1=m-1 := by simp <;> omega
    have hm : m-1+1=m := by have := i.isLt; omega
    simp only [numerator, ne_of_gt (Fin.castSucc_lt_succ (i := i)), if_false, if_true,
      not_lt_of_ge (Fin.castSucc_lt_succ (i := i)).le, he]
    simp only [Fin.val_succ, Fin.val_castSucc, Nat.add_sub_cancel_left,
      Nat.sub_self, pow_zero, mul_one, Nat.add_sub_cancel]
    rw [show (1-a)*(a*(1-a)^(m-1))=a*(1-a)^m by
      calc
        _ = a*(1-a)^((m-1)+1) := by rw [pow_succ]; ring
        _ = _ := by rw [hm]]
    simpa using H_right m a
  by_cases h1 : j=i.succ
  · subst j
    have he : m+1-i.succ.val+i.castSucc.val-1=m-1 := by simp <;> omega
    have hm : m-1+1=m := by have := i.isLt; omega
    simp only [numerator, if_true, ne_of_lt (Fin.castSucc_lt_succ (i := i)), if_false,
      Fin.castSucc_lt_succ, he, Fin.val_succ, Fin.val_castSucc,
      Nat.add_sub_cancel_left, Nat.sub_self, pow_zero, mul_one, Nat.add_sub_cancel]
    rw [show m+1-(i.val+1)+i.val-1=m-1 by have := i.isLt; omega]
    rw [show (1+a)*(-a*(1+a)^(m-1))= -a*(1+a)^m by
      calc
        _ = -a*(1+a)^((m-1)+1) := by rw [pow_succ]; ring
        _ = _ := by rw [hm]]
    simpa [sub_neg_eq_add] using H_left m a
  by_cases hj : j < i.castSucc
  · have hjs : j < i.succ := lt_trans hj (Fin.castSucc_lt_succ (i := i))
    have hx : i.succ.val-j.val-1=(i.castSucc.val-j.val-1)+1 := by
      simp only [Fin.val_succ, Fin.val_castSucc]
      simp only [Fin.lt_def, Fin.val_castSucc] at hj
      omega
    have hy : m+1-i.castSucc.val+j.val-1=(m+1-i.succ.val+j.val-1)+1 := by
      simp only [Fin.val_succ, Fin.val_castSucc]; have := i.isLt; omega
    simp only [numerator, Ne.symm h0, Ne.symm h1, if_false,
      not_lt_of_ge hj.le, not_lt_of_ge hjs.le, hx, hy, pow_succ]
    ring
  · have hjs : i.succ < j := by
      simp only [Fin.lt_def, Fin.val_succ, Fin.val_castSucc] at *
      have h0v : j.val≠i.val := by intro h; apply h0; exact Fin.ext h
      have h1v : j.val≠i.val+1 := by intro h; apply h1; exact Fin.ext h
      omega
    have hjc : i.castSucc < j := lt_trans (Fin.castSucc_lt_succ (i := i)) hjs
    have hx : m+1-j.val+i.succ.val-1=(m+1-j.val+i.castSucc.val-1)+1 := by
      simp only [Fin.val_succ, Fin.val_castSucc]; have := j.isLt; omega
    have hy : j.val-i.castSucc.val-1=(j.val-i.succ.val-1)+1 := by
      simp only [Fin.val_succ, Fin.val_castSucc]; simp only [Fin.lt_def, Fin.val_succ] at hjs; omega
    simp only [numerator, Ne.symm h0, Ne.symm h1, if_false, hjc, hjs, if_true,
      hx, hy, pow_succ]
    ring

lemma numerator_boundary (m : ℕ) (a : K) (j : Fin (m+1)) :
    (1-a)*numerator (m+1) a 0 j +
      (1+a)*numerator (m+1) a (Fin.last m) j =
    H (m+1) a * ((if (0 : Fin (m+1))=j then 1 else 0) +
      (if Fin.last m=j then 1 else 0)) := by
  by_cases hm : m=0
  · subst m
    have hj : j=0 := by apply Fin.ext; have := j.isLt; simp only [Fin.val_zero]; omega
    subst j
    simp [numerator, H]
  have hp : 0 < m := Nat.pos_of_ne_zero hm
  have hlast : (0 : Fin (m+1)) < Fin.last m := by simpa only [Fin.lt_def, Fin.val_zero, Fin.val_last] using hp
  by_cases h0 : j=0
  · subst j
    simp [numerator, ne_of_gt hlast, not_lt_of_ge hlast.le, Fin.val_last]
    have he : (1+a)*(a*(1+a)^(m-1))=a*(1+a)^m := by
      calc
        _ = a*(1+a)^((m-1)+1) := by rw [pow_succ]; ring
        _ = _ := by rw [Nat.sub_add_cancel hp]
    rw [he]
    exact H_left m a
  by_cases hl : j=Fin.last m
  · subst j
    simp [numerator, ne_of_lt hlast, hlast, Fin.val_last]
    have he : (1-a)*(a*(1-a)^(m-1))= a*(1-a)^m := by
      calc
        _ = a*(1-a)^((m-1)+1) := by rw [pow_succ]; ring
        _ = _ := by rw [Nat.sub_add_cancel hp]
    rw [he]
    have hh := H_right m a
    linear_combination -hh
  have hj0 : (0 : Fin (m+1)) < j := Fin.pos_iff_ne_zero.mpr h0
  have hjl : j < Fin.last m := by
    simp only [Fin.lt_def, Fin.val_last]
    have := j.isLt
    have hne : j.val≠m := by intro h; apply hl; exact Fin.ext h
    omega
  simp only [numerator, Ne.symm h0, Ne.symm hl, if_false, hj0, if_true,
    not_lt_of_ge hjl.le, Nat.add_sub_cancel, Fin.val_zero, Fin.val_last,
    Nat.sub_zero, Nat.add_zero]
  have hx : m+1-j.val-1=(m-j.val-1)+1 := by
    have := j.isLt; simp only [Fin.lt_def, Fin.val_last] at hjl; omega
  have hy : m+1-m+j.val-1=(j.val-1)+1 := by
    simp only [Fin.lt_def, Fin.val_zero] at hj0; omega
  rw [hx, hy, pow_succ, pow_succ]
  ring

/-- The polynomial candidate is an actual scaled inverse; this statement has
no nonvanishing hypothesis and includes a=0 and a=±1. -/
theorem kernel_mul_numerator (m : ℕ) (a : K) :
    TournamentHamiltonian.transitiveKernel (m+1) a * numerator (m+1) a =
      H (m+1) a • (1 : Matrix (Fin (m+1)) (Fin (m+1)) K) := by
  let C := TournamentHamiltonian.transitiveKernel (m+1) a * numerator (m+1) a -
    H (m+1) a • (1 : Matrix (Fin (m+1)) (Fin (m+1)) K)
  have hd (i : Fin m) (j : Fin (m+1)) : C i.succ j - C i.castSucc j=0 := by
    have hA : (TournamentHamiltonian.transitiveKernel (m+1) a * numerator (m+1) a) i.succ j -
        (TournamentHamiltonian.transitiveKernel (m+1) a * numerator (m+1) a) i.castSucc j =
      -(1+a)*numerator (m+1) a i.castSucc j+(1-a)*numerator (m+1) a i.succ j := by
      simp only [Matrix.mul_apply, ← Finset.sum_sub_distrib, ← sub_mul, kernel_row_difference]
      simp [add_mul, Finset.sum_add_distrib, mul_assoc, Finset.mul_sum]
    have hB := numerator_row_difference m a i j
    dsimp [C]
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
    linear_combination hA + hB
  have hc (i j : Fin (m+1)) : C i j=C 0 j := by
    induction i using Fin.induction with
    | zero => rfl
    | succ i ih => exact (sub_eq_zero.mp (hd i j)).trans ih
  have hb (j : Fin (m+1)) : C 0 j+C (Fin.last m) j=0 := by
    have hA : (TournamentHamiltonian.transitiveKernel (m+1) a * numerator (m+1) a) 0 j +
        (TournamentHamiltonian.transitiveKernel (m+1) a * numerator (m+1) a) (Fin.last m) j =
      (1-a)*numerator (m+1) a 0 j+(1+a)*numerator (m+1) a (Fin.last m) j := by
      simp only [Matrix.mul_apply, ← Finset.sum_add_distrib, ← add_mul, kernel_boundary]
      simp [add_mul, Finset.sum_add_distrib, mul_assoc, Finset.mul_sum]
    have hB := numerator_boundary m a j
    dsimp [C]
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
    linear_combination hA + hB
  have hz (i j : Fin (m+1)) : C i j=0 := by
    have hh := hb j
    rw [hc (Fin.last m) j] at hh
    have h2 : (2 : K)*C 0 j=0 := by linear_combination hh
    rw [hc i j]
    exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
  ext i j
  exact sub_eq_zero.mp (hz i j)

/-- Explicit genuine inverse whenever the finite scalar denominator is nonzero. -/
theorem inverse_formula (m : ℕ) (a : K) (h : H (m+1) a ≠ 0) :
    (TournamentHamiltonian.transitiveKernel (m+1) a)⁻¹ =
      (H (m+1) a)⁻¹ • numerator (m+1) a := by
  apply Matrix.inv_eq_right_inv
  rw [Matrix.mul_smul, kernel_mul_numerator, smul_smul]
  simp [h]

end TransitiveKernelInverse
#print axioms TransitiveKernelInverse.kernel_mul_numerator

#print axioms TransitiveKernelInverse.inverse_formula
