import ActualTournamentDeletionEnergy

/-!
Exact finite prescaling mass identity from the corrected G1 proof. In particular
it retains +W and the ordered cross term w^T S v. This is algebra for actual
pre-scaled matrices, not an assumption of the sought global energy bound.
Focused Lean checks are recorded alongside this file.
-/
noncomputable section
namespace TournamentPrescalingMass
open Finset

variable {n : ℕ}

def bilinear (S : Matrix (Fin n) (Fin n) ℝ) (x y : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, x i * S i j * y j

def v (a : Fin n → ℝ) (i : Fin n) : ℝ := a i / (1 - (a i)^2)
def w (a : Fin n → ℝ) (i : Fin n) : ℝ := (a i)^2 / (1 - (a i)^2)
def ell (a : Fin n → ℝ) (i : Fin n) : ℝ := (1 + a i)⁻¹
def rightScale (a : Fin n → ℝ) (i : Fin n) : ℝ := (1 - a i)⁻¹

def rawMass (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, ell a i * (1 - (if i = j then 1 else 0) + S i j) * rightScale a j

def massExcess (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) : ℝ :=
  rawMass S a / ((n : ℝ) - 1) - n

lemma one_sub_sq_ne {x : ℝ} (hx : |x| < 1) : 1 - x^2 ≠ 0 := by
  exact ne_of_gt (sub_pos.mpr ((sq_lt_one_iff_abs_lt_one x).mpr hx))

lemma ell_decomposition (a : Fin n → ℝ) (ha : ∀ i, |a i| < 1) (i : Fin n) :
    ell a i = 1 + w a i - v a i := by
  have hden := one_sub_sq_ne (ha i)
  have hplus : 1 + a i ≠ 0 := by have hh := abs_lt.mp (ha i); linarith
  dsimp [ell, w, v]
  field_simp [hden, hplus]; ring

lemma right_decomposition (a : Fin n → ℝ) (ha : ∀ i, |a i| < 1) (i : Fin n) :
    rightScale a i = 1 + w a i + v a i := by
  have hden := one_sub_sq_ne (ha i)
  have hminus : 1 - a i ≠ 0 := by have hh := abs_lt.mp (ha i); linarith
  dsimp [rightScale, w, v]
  field_simp [hden, hminus]; ring

lemma scale_product (a : Fin n → ℝ) (ha : ∀ i, |a i| < 1) (i : Fin n) :
    ell a i * rightScale a i = 1 + w a i := by
  have hden := one_sub_sq_ne (ha i)
  have hplus : 1 + a i ≠ 0 := by have hh := abs_lt.mp (ha i); linarith
  have hminus : 1 - a i ≠ 0 := by have hh := abs_lt.mp (ha i); linarith
  dsimp [ell, rightScale, w]
  field_simp [hden, hplus, hminus]; ring

lemma a_mul_v (a : Fin n → ℝ) (i : Fin n) : a i * v a i = w a i := by
  simp only [v, w]
  ring

lemma bilinear_add_left (S : Matrix (Fin n) (Fin n) ℝ) (x y z : Fin n → ℝ) :
    bilinear S (x + y) z = bilinear S x z + bilinear S y z := by
  simp [bilinear, add_mul, sum_add_distrib]

lemma bilinear_sub_left (S : Matrix (Fin n) (Fin n) ℝ) (x y z : Fin n → ℝ) :
    bilinear S (x - y) z = bilinear S x z - bilinear S y z := by
  simp [bilinear, sub_mul, sum_sub_distrib]

lemma bilinear_add_right (S : Matrix (Fin n) (Fin n) ℝ) (x y z : Fin n → ℝ) :
    bilinear S x (y + z) = bilinear S x y + bilinear S x z := by
  simp [bilinear, mul_add, sum_add_distrib]

lemma bilinear_skew (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : ∀ i j, S i j = - S j i) (x y : Fin n → ℝ) :
    bilinear S x y = -bilinear S y x := by
  unfold bilinear
  rw [sum_comm, ← sum_neg_distrib]
  apply sum_congr rfl
  intro j hj
  rw [← sum_neg_distrib]
  apply sum_congr rfl
  intro i hi
  rw [hS i j]
  ring

lemma bilinear_self_zero (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : ∀ i j, S i j = - S j i) (x : Fin n → ℝ) : bilinear S x x = 0 := by
  linarith [bilinear_skew S hS x x]

lemma bilinear_cross (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : ∀ i j, S i j = - S j i) (x y : Fin n → ℝ) :
    bilinear S (x - y) (x + y) = 2 * bilinear S x y := by
  rw [bilinear_sub_left, bilinear_add_right, bilinear_add_right,
    bilinear_self_zero S hS x, bilinear_self_zero S hS y, bilinear_skew S hS y x]
  ring

lemma bilinear_one (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : ∀ i j, S i j = - S j i) (a y : Fin n → ℝ) (c : ℝ)
    (hscore : ∀ i, ∑ j, S i j = c * a i) :
    bilinear S (fun _ => 1) y = -c * ∑ j, a j * y j := by
  have hcol (j : Fin n) : (∑ i, S i j) = -(c * a j) := by
    calc
      _ = ∑ i, - S j i := sum_congr rfl (fun i _ => hS i j)
      _ = -(∑ i, S j i) := by simp
      _ = _ := by rw [hscore]
  unfold bilinear
  simp only [one_mul]
  rw [sum_comm]
  simp_rw [← sum_mul, hcol]
  rw [mul_sum]
  apply sum_congr rfl
  intro j hj
  ring

lemma rawMass_decomposition (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) :
    rawMass S a = (∑ i, ell a i) * (∑ j, rightScale a j) -
      (∑ i, ell a i * rightScale a i) + bilinear S (ell a) (rightScale a) := by
  have he (i j : Fin n) :
      ell a i * (1 - (if i = j then 1 else 0) + S i j) * rightScale a j =
      ell a i * rightScale a j -
      (if i = j then ell a i * rightScale a i else 0) +
      ell a i * S i j * rightScale a j := by
    by_cases hij : i = j <;> simp [hij]; ring
  unfold rawMass bilinear
  simp_rw [he]
  simp only [sum_add_distrib, sum_sub_distrib]
  simp [← mul_sum, ← sum_mul]

/-- Corrected exact numerator, before dividing by n-1. -/
theorem rawMass_identity (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : ∀ i j, S i j = - S j i) (a : Fin n → ℝ)
    (ha : ∀ i, |a i| < 1)
    (hscore : ∀ i, ∑ j, S i j = ((n : ℝ) - 1) * a i) :
    rawMass S a = (n : ℝ) * ((n : ℝ) - 1) +
      (∑ i, w a i)^2 - (∑ i, v a i)^2 + (∑ i, w a i) +
      2 * bilinear S (w a) (v a) := by
  let x : Fin n → ℝ := fun i => 1 + w a i
  have hl : ell a = x - v a := funext (ell_decomposition a ha)
  have hr : rightScale a = x + v a := funext (right_decomposition a ha)
  have hsL : (∑ i, ell a i) = (n : ℝ) + (∑ i, w a i) - ∑ i, v a i := by
    simp_rw [ell_decomposition a ha]
    simp [sum_add_distrib, sum_sub_distrib]
  have hsR : (∑ i, rightScale a i) = (n : ℝ) + (∑ i, w a i) + ∑ i, v a i := by
    simp_rw [right_decomposition a ha]
    simp [sum_add_distrib]
  have hsD : (∑ i, ell a i * rightScale a i) = (n : ℝ) + ∑ i, w a i := by
    simp_rw [scale_product a ha]
    simp [sum_add_distrib]
  have hx : x = (fun _ => 1) + w a := rfl
  have hcross : bilinear S (ell a) (rightScale a) =
      -2 * ((n : ℝ) - 1) * (∑ i, w a i) + 2 * bilinear S (w a) (v a) := by
    rw [hl, hr, bilinear_cross S hS, hx, bilinear_add_left,
      bilinear_one S hS a (v a) ((n : ℝ) - 1) hscore]
    simp_rw [a_mul_v]
    ring
  rw [rawMass_decomposition, hsL, hsR, hsD, hcross]
  ring

/-- The diagonal +W and the ordered term +2 w^T S v are both present. -/
theorem massExcess_identity (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : ∀ i j, S i j = - S j i) (a : Fin n → ℝ)
    (ha : ∀ i, |a i| < 1) (hn : (n : ℝ) - 1 ≠ 0)
    (hscore : ∀ i, ∑ j, S i j = ((n : ℝ) - 1) * a i) :
    massExcess S a =
      ((∑ i, w a i)^2 - (∑ i, v a i)^2 + (∑ i, w a i) +
        2 * bilinear S (w a) (v a)) / ((n : ℝ) - 1) := by
  rw [massExcess, rawMass_identity S hS a ha hscore]
  field_simp [hn]; ring

/-- Specialization to the same actual Boolean tournament as the path count. -/
theorem actual_tournament_massExcess (T : TournamentHamiltonian.Tournament n) (hn : 2 ≤ n)
    (ha : ∀ i, |TournamentHamiltonian.score T i / ((n : ℝ) - 1)| < 1) :
    let a := fun i => TournamentHamiltonian.score T i / ((n : ℝ) - 1)
    massExcess (TournamentHamiltonian.signMatrix T) a =
      ((∑ i, w a i)^2 - (∑ i, v a i)^2 + (∑ i, w a i) +
        2 * bilinear (TournamentHamiltonian.signMatrix T) (w a) (v a)) /
          ((n : ℝ) - 1) := by
  have hnR : (n : ℝ) - 1 ≠ 0 := by
    have hh : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  apply massExcess_identity _ (TournamentHamiltonian.signMatrix_skew T) _ ha hnR
  intro i
  change TournamentHamiltonian.score T i =
    ((n : ℝ) - 1) * (TournamentHamiltonian.score T i / ((n : ℝ) - 1))
  field_simp [hnR]

end TournamentPrescalingMass
#print axioms TournamentPrescalingMass.rawMass_identity
#print axioms TournamentPrescalingMass.massExcess_identity
#print axioms TournamentPrescalingMass.actual_tournament_massExcess
