import IndependentDeletionMass
import Mathlib.Analysis.Convex.DoublyStochasticMatrix

/-!
Finite mass-potential inequalities for an already existing diagonal scaling.
Focused compiled candidate. This file does not assert existence of scaling parameters.
The proof uses exp(-z) >= 1-z entrywise, not an assumed potential inequality.
Different row and column index types are allowed, including independent minors.
-/
noncomputable section
namespace MatrixScalingMassPotential
open Finset
variable {α β : Type*} [Fintype α] [Fintype β]

def expScaled (M : Matrix α β ℝ) (x : α → ℝ) (y : β → ℝ) : Matrix α β ℝ :=
  fun i j => M i j * Real.exp (x i + y j)

def totalMass (M : Matrix α β ℝ) : ℝ := ∑ i, ∑ j, M i j

def theta (x : α → ℝ) (y : β → ℝ) : ℝ := (∑ i, x i) + ∑ j, y j

def kappa (M : Matrix α β ℝ) : ℝ := totalMass M - (Fintype.card α : ℝ)

lemma expScaled_nonneg (M : Matrix α β ℝ) (x : α → ℝ) (y : β → ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (i : α) (j : β) :
    0 ≤ expScaled M x y i j :=
  mul_nonneg (hM i j) (Real.exp_pos _).le

lemma expScaled_unscale_entry (M : Matrix α β ℝ) (x : α → ℝ) (y : β → ℝ)
    (i : α) (j : β) :
    expScaled M x y i j * Real.exp (-(x i + y j)) = M i j := by
  unfold expScaled
  rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

lemma totalMass_of_rows (N : Matrix α β ℝ) (hrow : ∀ i, (∑ j, N i j) = 1) :
    totalMass N = (Fintype.card α : ℝ) := by
  unfold totalMass
  simp_rw [hrow]
  simp

/-- Both marginal equalities are used. No target potential bound is a premise. -/
lemma weighted_theta (N : Matrix α β ℝ) (x : α → ℝ) (y : β → ℝ)
    (hrow : ∀ i, (∑ j, N i j) = 1) (hcol : ∀ j, (∑ i, N i j) = 1) :
    (∑ i, ∑ j, N i j * (x i + y j)) = theta x y := by
  have hx : (∑ i, ∑ j, N i j * x i) = ∑ i, x i := by
    apply sum_congr rfl
    intro i hi
    rw [← sum_mul, hrow, one_mul]
  have hy : (∑ i, ∑ j, N i j * y j) = ∑ j, y j := by
    rw [sum_comm]
    apply sum_congr rfl
    intro j hj
    rw [← sum_mul, hcol, one_mul]
  simp_rw [mul_add, sum_add_distrib]
  rw [hx, hy]
  rfl

/-- The exact finite capacity direction for a mass m+kappa matrix.
There is no smallness, density, spectral-gap, or positivity-of-every-entry premise.
Only nonnegativity and the actual row/column equations of an existing scaling
are required. In particular this theorem does not construct that scaling. -/
theorem theta_ge_neg_kappa (M : Matrix α β ℝ) (x : α → ℝ) (y : β → ℝ)
    (hM : ∀ i j, 0 ≤ M i j)
    (hrow : ∀ i, (∑ j, expScaled M x y i j) = 1)
    (hcol : ∀ j, (∑ i, expScaled M x y i j) = 1) :
    -kappa M ≤ theta x y := by
  have hpoint (i : α) (j : β) :
      expScaled M x y i j * (1 - (x i + y j)) ≤ M i j := by
    have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-(x i + y j)))
      (expScaled_nonneg M x y hM i j)
    rw [expScaled_unscale_entry] at h
    convert h using 1 <;> ring
  have hsum := sum_le_sum (s := (univ : Finset α)) (fun i _ =>
    sum_le_sum (s := (univ : Finset β)) (fun j _ => hpoint i j))
  have hleft : (∑ i, ∑ j, expScaled M x y i j * (1 - (x i + y j))) =
      (Fintype.card α : ℝ) - theta x y := by
    simp_rw [mul_sub, mul_one, sum_sub_distrib]
    rw [weighted_theta _ _ _ hrow hcol]
    rw [show (∑ i, ∑ j, expScaled M x y i j) = (Fintype.card α : ℝ) from
      totalMass_of_rows _ hrow]
  rw [hleft] at hsum
  unfold kappa totalMass
  linarith only [hsum]

/-- The multiplicative loss used for nonprincipal permanent recovery. -/
theorem exp_neg_theta_le_exp_kappa (M : Matrix α β ℝ) (x : α → ℝ) (y : β → ℝ)
    (hM : ∀ i j, 0 ≤ M i j)
    (hrow : ∀ i, (∑ j, expScaled M x y i j) = 1)
    (hcol : ∀ j, (∑ i, expScaled M x y i j) = 1) :
    Real.exp (-theta x y) ≤ Real.exp (kappa M) := by
  apply Real.exp_le_exp.mpr
  linarith [theta_ge_neg_kappa M x y hM hrow hcol]

/-- Zero total mass error is the extra premise needed for theta >= 0. -/
theorem theta_nonneg_of_exact_mass (M : Matrix α β ℝ) (x : α → ℝ) (y : β → ℝ)
    (hM : ∀ i j, 0 ≤ M i j)
    (hrow : ∀ i, (∑ j, expScaled M x y i j) = 1)
    (hcol : ∀ j, (∑ i, expScaled M x y i j) = 1)
    (hmass : totalMass M = (Fintype.card α : ℝ)) :
    0 ≤ theta x y := by
  have h := theta_ge_neg_kappa M x y hM hrow hcol
  simpa [kappa, hmass] using h

section Square
variable [DecidableEq α]

/-- Direct compatibility with mathlib's existing doubly-stochastic predicate. -/
theorem theta_ge_neg_kappa_of_doublyStochastic (M : Matrix α α ℝ)
    (x y : α → ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (hscale : expScaled M x y ∈ doublyStochastic ℝ α) :
    -kappa M ≤ theta x y := by
  exact theta_ge_neg_kappa M x y hM
    (sum_row_of_mem_doublyStochastic hscale)
    (sum_col_of_mem_doublyStochastic hscale)

end Square

section IndependentMinor
variable {n : ℕ}

/-- The literal independently deleted matrix X, with distinct subtype indices. -/
def deletionMatrix (A : Matrix (Fin n) (Fin n) ℝ) (I J : Finset (Fin n)) :
    Matrix (Iᶜ : Finset (Fin n)) (Jᶜ : Finset (Fin n)) ℝ :=
  fun i j => (n : ℝ) / ((n : ℝ) - I.card) * A i.val j.val

lemma deletionMatrix_totalMass (A : Matrix (Fin n) (Fin n) ℝ)
    (I J : Finset (Fin n)) :
    totalMass (deletionMatrix A I J) =
      (n : ℝ) / ((n : ℝ) - I.card) * IndependentDeletionMass.remainingMass A I J := by
  unfold totalMass deletionMatrix
  simp_rw [← mul_sum]
  congr 1
  unfold IndependentDeletionMass.remainingMass IndependentDeletionMass.crossMass
  calc
    (∑ i : (Iᶜ : Finset (Fin n)), ∑ j : (Jᶜ : Finset (Fin n)), A i.val j.val) =
        ∑ i : (Iᶜ : Finset (Fin n)), ∑ j ∈ Jᶜ, A i.val j := by
      apply sum_congr rfl
      intro i hi
      exact Finset.sum_coe_sort (Jᶜ : Finset (Fin n)) (fun j => A i.val j)
    _ = _ := Finset.sum_coe_sort (Iᶜ : Finset (Fin n)) (fun i => ∑ j ∈ Jᶜ, A i j)

/-- The generic mass error is exactly the already verified independent kappa. -/
theorem deletionMatrix_kappa (A : Matrix (Fin n) (Fin n) ℝ)
    (I J : Finset (Fin n)) :
    kappa (deletionMatrix A I J) = IndependentDeletionMass.deletionExcess A I J := by
  have hc : (Fintype.card (Iᶜ : Finset (Fin n)) : ℝ) = (n : ℝ) - I.card := by
    rw [Fintype.card_coe, card_compl, Nat.cast_sub (card_le_univ I)]
    simp
  unfold kappa IndependentDeletionMass.deletionExcess
  rw [deletionMatrix_totalMass, hc]

/-- Independent row and column deletions are allowed. Scaling existence is an
explicitly remaining obligation, represented by the actual balance equations. -/
theorem theta_ge_neg_deletionExcess (A : Matrix (Fin n) (Fin n) ℝ)
    (I J : Finset (Fin n)) (ht : I.card < n) (hA : ∀ i j, 0 ≤ A i j)
    (x : (Iᶜ : Finset (Fin n)) → ℝ) (y : (Jᶜ : Finset (Fin n)) → ℝ)
    (hrow : ∀ i, (∑ j, expScaled (deletionMatrix A I J) x y i j) = 1)
    (hcol : ∀ j, (∑ i, expScaled (deletionMatrix A I J) x y i j) = 1) :
    -IndependentDeletionMass.deletionExcess A I J ≤ theta x y := by
  have htR : (I.card : ℝ) < n := by exact_mod_cast ht
  have hX : ∀ i j, 0 ≤ deletionMatrix A I J i j := by
    intro i j
    exact mul_nonneg (div_nonneg (Nat.cast_nonneg n) (by linarith)) (hA i.val j.val)
  have h := theta_ge_neg_kappa (deletionMatrix A I J) x y hX hrow hcol
  rw [deletionMatrix_kappa] at h
  exact h

end IndependentMinor

end MatrixScalingMassPotential
#print axioms MatrixScalingMassPotential.weighted_theta
#print axioms MatrixScalingMassPotential.theta_ge_neg_kappa
#print axioms MatrixScalingMassPotential.exp_neg_theta_le_exp_kappa
#print axioms MatrixScalingMassPotential.theta_nonneg_of_exact_mass
#print axioms MatrixScalingMassPotential.theta_ge_neg_kappa_of_doublyStochastic

#print axioms MatrixScalingMassPotential.deletionMatrix_kappa
#print axioms MatrixScalingMassPotential.theta_ge_neg_deletionExcess
