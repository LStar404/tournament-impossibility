import Mathlib

/-!
Exact mass accounting for independently deleted rows and columns. The matrix
is normalized to total mass n before deletion; it need not be doubly stochastic.
The terminal -t^2/n term is retained. Focused Lean checks are recorded alongside this file. This is not a scaling
existence theorem or a global extremal entry theorem.
-/
noncomputable section
namespace IndependentDeletionMass
open Finset
variable {n : ℕ}

def rowResidual (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : ℝ := (∑ j, A i j) - 1
def colResidual (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) : ℝ := (∑ i, A i j) - 1

def crossMass (A : Matrix (Fin n) (Fin n) ℝ) (I J : Finset (Fin n)) : ℝ :=
  ∑ i ∈ I, ∑ j ∈ J, A i j

def remainingMass (A : Matrix (Fin n) (Fin n) ℝ) (I J : Finset (Fin n)) : ℝ :=
  crossMass A Iᶜ Jᶜ

/-- Mass of X=(n/(n-t))*A[I-complement,J-complement], minus its dimension n-t. -/
def deletionExcess (A : Matrix (Fin n) (Fin n) ℝ) (I J : Finset (Fin n)) : ℝ :=
  (n : ℝ) / ((n : ℝ) - I.card) * remainingMass A I J - ((n : ℝ) - I.card)

lemma row_split (A : Matrix (Fin n) (Fin n) ℝ) (I J : Finset (Fin n)) :
    crossMass A I J + crossMass A I Jᶜ = ∑ i ∈ I, ∑ j, A i j := by
  rw [crossMass, crossMass, ← sum_add_distrib]
  apply sum_congr rfl
  intro i hi
  exact sum_add_sum_compl J (fun j => A i j)

lemma col_split (A : Matrix (Fin n) (Fin n) ℝ) (I J : Finset (Fin n)) :
    crossMass A I J + crossMass A Iᶜ J = ∑ j ∈ J, ∑ i, A i j := by
  have hI : crossMass A I J = ∑ j ∈ J, ∑ i ∈ I, A i j := by
    unfold crossMass
    exact sum_comm
  have hcI : crossMass A Iᶜ J = ∑ j ∈ J, ∑ i ∈ Iᶜ, A i j := by
    unfold crossMass
    exact sum_comm
  rw [hI, hcI, ← sum_add_distrib]
  apply sum_congr rfl
  intro j hj
  exact sum_add_sum_compl I (fun i => A i j)

lemma remainingMass_inclusion_exclusion (A : Matrix (Fin n) (Fin n) ℝ)
    (I J : Finset (Fin n)) :
    remainingMass A I J = (∑ i, ∑ j, A i j) -
      (∑ i ∈ I, ∑ j, A i j) - (∑ j ∈ J, ∑ i, A i j) + crossMass A I J := by
  have hr := sum_add_sum_compl I (fun i => ∑ j, A i j)
  have hI := row_split A I J
  have hcI := row_split A Iᶜ J
  have hJ := col_split A I J
  change crossMass A Iᶜ Jᶜ = _
  linarith

lemma row_mass_eq_residual (A : Matrix (Fin n) (Fin n) ℝ) (I : Finset (Fin n)) :
    (∑ i ∈ I, ∑ j, A i j) = (I.card : ℝ) + ∑ i ∈ I, rowResidual A i := by
  simp only [rowResidual, sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one]
  ring

lemma col_mass_eq_residual (A : Matrix (Fin n) (Fin n) ℝ) (J : Finset (Fin n)) :
    (∑ j ∈ J, ∑ i, A i j) = (J.card : ℝ) + ∑ j ∈ J, colResidual A j := by
  simp only [colResidual, sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one]
  ring

/-- Independent row/column deletion, not restricted to principal minors. -/
theorem remainingMass_exact (A : Matrix (Fin n) (Fin n) ℝ)
    (I J : Finset (Fin n)) (hmass : (∑ i, ∑ j, A i j) = n)
    (hcard : J.card = I.card) :
    remainingMass A I J = (n : ℝ) - 2 * (I.card : ℝ) -
      (∑ i ∈ I, rowResidual A i) - (∑ j ∈ J, colResidual A j) + crossMass A I J := by
  rw [remainingMass_inclusion_exclusion, hmass, row_mass_eq_residual,
    col_mass_eq_residual, hcard]
  ring

/-- Exact numerator of kappa. Even exact marginal normalization does not let
one drop the -t^2 term independently of the cross block. -/
theorem deletionExcess_exact (A : Matrix (Fin n) (Fin n) ℝ)
    (I J : Finset (Fin n)) (hmass : (∑ i, ∑ j, A i j) = n)
    (hcard : J.card = I.card) (ht : I.card < n) :
    deletionExcess A I J =
      ((n : ℝ) * crossMass A I J - (n : ℝ) * (∑ i ∈ I, rowResidual A i) -
        (n : ℝ) * (∑ j ∈ J, colResidual A j) - (I.card : ℝ)^2) /
          ((n : ℝ) - I.card) := by
  have htR : (I.card : ℝ) < n := by exact_mod_cast ht
  have hne : (n : ℝ) - I.card ≠ 0 := by linarith
  rw [deletionExcess, remainingMass_exact A I J hmass hcard]
  field_simp [hne]; ring

theorem deletionExcess_factored (A : Matrix (Fin n) (Fin n) ℝ)
    (I J : Finset (Fin n)) (hmass : (∑ i, ∑ j, A i j) = n)
    (hcard : J.card = I.card) (ht : I.card < n) :
    deletionExcess A I J = (n : ℝ) / ((n : ℝ) - I.card) *
      (crossMass A I J - (∑ i ∈ I, rowResidual A i) -
        (∑ j ∈ J, colResidual A j) - (I.card : ℝ)^2 / n) := by
  have hn : 0 < n := by omega
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  rw [deletionExcess_exact A I J hmass hcard ht]
  field_simp [hnR]

lemma abs_sum_le_card_mul {ι : Type*} (I : Finset ι) (f : ι → ℝ)
    (d : ℝ) (hf : ∀ i ∈ I, |f i| ≤ d) : |∑ i ∈ I, f i| ≤ I.card * d := by
  calc
    _ ≤ ∑ i ∈ I, |f i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ I, d := sum_le_sum hf
    _ = _ := by simp

lemma crossMass_abs_le (A : Matrix (Fin n) (Fin n) ℝ)
    (I J : Finset (Fin n)) {C : ℝ} (_hC : 0 ≤ C) (_hn : 0 < n)
    (hentry : ∀ i j, |A i j| ≤ C / n) :
    |crossMass A I J| ≤ C * (I.card : ℝ) * (J.card : ℝ) / n := by
  have hrow (i : Fin n) : |∑ j ∈ J, A i j| ≤ (J.card : ℝ) * (C / n) :=
    abs_sum_le_card_mul J (fun j => A i j) (C / n) (fun j _ => hentry i j)
  have h := abs_sum_le_card_mul I (fun i => ∑ j ∈ J, A i j)
    ((J.card : ℝ) * (C / n)) (fun i _ => hrow i)
  change |crossMass A I J| ≤ _ at h
  convert h using 1; ring

/-- Finite kappa estimate from entry and marginal errors. These assumptions
are properties of the original normalized matrix, not a bound on kappa. -/
theorem deletionExcess_bound (A : Matrix (Fin n) (Fin n) ℝ)
    (I J : Finset (Fin n)) (hmass : (∑ i, ∑ j, A i j) = n)
    (hcard : J.card = I.card) (hn : 0 < n) (hhalf : 2 * I.card ≤ n)
    {C d : ℝ} (hC : 0 ≤ C) (_hd : 0 ≤ d)
    (hentry : ∀ i j, |A i j| ≤ C / n)
    (hrow : ∀ i, |rowResidual A i| ≤ d)
    (hcol : ∀ j, |colResidual A j| ≤ d) :
    |deletionExcess A I J| ≤
      4 * (I.card : ℝ) * d + 2 * (C + 1) * (I.card : ℝ)^2 / n := by
  have ht : I.card < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have htR : (I.card : ℝ) < n := by exact_mod_cast ht
  have hhalfR : 2 * (I.card : ℝ) ≤ n := by exact_mod_cast hhalf
  have hnm : 0 < (n : ℝ) - I.card := by linarith
  have hscale0 : 0 ≤ (n : ℝ) / ((n : ℝ) - I.card) := div_nonneg hnR.le hnm.le
  have hscale : (n : ℝ) / ((n : ℝ) - I.card) ≤ 2 :=
    (div_le_iff₀ hnm).mpr (by linarith)
  have hx := crossMass_abs_le A I J hC hn hentry
  rw [hcard] at hx
  have hr := abs_sum_le_card_mul I (rowResidual A) d (fun i _ => hrow i)
  have hc := abs_sum_le_card_mul J (colResidual A) d (fun j _ => hcol j)
  rw [hcard] at hc
  have hsquare : 0 ≤ (I.card : ℝ)^2 / n := div_nonneg (sq_nonneg _) hnR.le
  have hinner : |crossMass A I J - (∑ i ∈ I, rowResidual A i) -
        (∑ j ∈ J, colResidual A j) - (I.card : ℝ)^2 / n| ≤
      2 * (I.card : ℝ) * d + (C + 1) * (I.card : ℝ)^2 / n := by
    have ha := abs_sub (crossMass A I J) (∑ i ∈ I, rowResidual A i)
    have hb := abs_sub (crossMass A I J - (∑ i ∈ I, rowResidual A i))
      (∑ j ∈ J, colResidual A j)
    have he := abs_sub (crossMass A I J - (∑ i ∈ I, rowResidual A i) -
      (∑ j ∈ J, colResidual A j)) ((I.card : ℝ)^2 / n)
    rw [abs_of_nonneg hsquare] at he
    have hxp : C * (I.card : ℝ) * (I.card : ℝ) / n = C * (I.card : ℝ)^2 / n := by ring
    rw [hxp] at hx
    calc
      _ ≤ C * (I.card : ℝ)^2 / n + (I.card : ℝ) * d +
          (I.card : ℝ) * d + (I.card : ℝ)^2 / n := by linarith
      _ = _ := by ring
  rw [deletionExcess_factored A I J hmass hcard ht, abs_mul, abs_of_nonneg hscale0]
  calc
    _ ≤ 2 * (2 * (I.card : ℝ) * d + (C + 1) * (I.card : ℝ)^2 / n) :=
      mul_le_mul hscale hinner (abs_nonneg _) (by norm_num)
    _ = _ := by ring

/-- A uniform matrix has kappa exactly zero; the cross block cancels t^2/n. -/
theorem uniform_deletionExcess (I J : Finset (Fin n))
    (hcard : J.card = I.card) (hn : 0 < n) (ht : I.card < n) :
    deletionExcess (fun _ _ => (n : ℝ)⁻¹) I J = 0 := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have htR : (I.card : ℝ) < n := by exact_mod_cast ht
  have hmR : (n : ℝ) - I.card ≠ 0 := by linarith
  have hi : ((Iᶜ).card : ℝ) = (n : ℝ) - I.card := by
    rw [card_compl, Nat.cast_sub (card_le_univ I)]
    simp
  have hj : ((Jᶜ).card : ℝ) = (n : ℝ) - I.card := by
    rw [card_compl, Nat.cast_sub (card_le_univ J), hcard]
    simp
  simp only [deletionExcess, remainingMass, crossMass, sum_const, nsmul_eq_mul]
  rw [hi, hj]
  field_simp [hnR, hmR]; ring

end IndependentDeletionMass
#print axioms IndependentDeletionMass.remainingMass_exact
#print axioms IndependentDeletionMass.deletionExcess_exact
#print axioms IndependentDeletionMass.deletionExcess_bound
#print axioms IndependentDeletionMass.uniform_deletionExcess

#print axioms IndependentDeletionMass.deletionExcess_factored
