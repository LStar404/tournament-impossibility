import NonprincipalReconstructionCandidate
import ActualTournamentPrescalingBounds
import Mathlib

/-! Isolated bounds for the actual reconstruction factor
NonprincipalReconstructionCandidate.gamma, not a new surrogate product.
No path-count or determinant comparison is inferred from these scalar bounds. -/
set_option autoImplicit false
noncomputable section
namespace ActualGammaBoundsCandidate
open Finset NonprincipalReconstructionCandidate TournamentPrescalingMassBound
open TournamentHamiltonian ActualTournamentPrescalingBounds
variable {n : ℕ}

lemma factor_log_bounds (x b : ℝ) (hb0 : 0 ≤ b) (hb1 : b < 1) (hx : |x| ≤ b) :
    -(x^2)/(1-b^2) ≤ Real.log (1-x^2) ∧ Real.log (1-x^2) ≤ -(x^2) := by
  have hb := base_denominator_pos hb0 hb1
  have hd := coordinate_denominator_pos hb0 hb1 hx
  have hs := coordinate_sq_le hb0 hx
  have hratio : x^2/(1-x^2) ≤ x^2/(1-b^2) :=
    div_le_div_of_nonneg_left (sq_nonneg x) hb (by linarith)
  have hl := Real.one_sub_inv_le_log_of_pos hd
  have he : 1-(1-x^2)⁻¹ = -(x^2)/(1-x^2) := by
    field_simp [hd.ne']
    ring
  rw [he] at hl
  constructor
  · exact (show -(x^2)/(1-b^2) ≤ -(x^2)/(1-x^2) by
      simpa only [neg_div] using neg_le_neg hratio).trans hl
  · have hu := Real.log_le_sub_one_of_pos hd
    linarith

lemma gamma_pos (a : Fin n → ℝ) (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (ha : ∀ i, |a i| ≤ b) : 0 < gamma a := by
  unfold gamma
  exact prod_pos (fun i _ => coordinate_denominator_pos hb0 hb1 (ha i))

lemma log_gamma (a : Fin n → ℝ) (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (ha : ∀ i, |a i| ≤ b) : Real.log (gamma a) = ∑ i, Real.log (1-(a i)^2) := by
  unfold gamma
  exact Real.log_prod (fun i _ => (coordinate_denominator_pos hb0 hb1 (ha i)).ne')

theorem log_gamma_bounds (a : Fin n → ℝ) (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (ha : ∀ i, |a i| ≤ b) :
    -(tau a)/(1-b^2) ≤ Real.log (gamma a) ∧ Real.log (gamma a) ≤ -(tau a) := by
  rw [log_gamma a b hb0 hb1 ha]
  constructor
  · calc
      _ = ∑ i, -((a i)^2)/(1-b^2) := by
        simp only [← sum_div, sum_neg_distrib, tau]
      _ ≤ _ := sum_le_sum (fun i _ => (factor_log_bounds (a i) b hb0 hb1 (ha i)).1)
  · calc
      _ ≤ ∑ i, -((a i)^2) := sum_le_sum
        (fun i _ => (factor_log_bounds (a i) b hb0 hb1 (ha i)).2)
      _ = _ := by simp only [sum_neg_distrib, tau]

/-- Both sides retain exactly the Gamma appearing in actual reconstruction. -/
theorem gamma_exp_bounds (a : Fin n → ℝ) (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (ha : ∀ i, |a i| ≤ b) :
    Real.exp (-(tau a)/(1-b^2)) ≤ gamma a ∧ gamma a ≤ Real.exp (-(tau a)) := by
  have hp := gamma_pos a b hb0 hb1 ha
  have hh := log_gamma_bounds a b hb0 hb1 ha
  constructor
  · calc
      _ ≤ Real.exp (Real.log (gamma a)) := Real.exp_le_exp.mpr hh.1
      _ = _ := Real.exp_log hp
  · calc
      _ = Real.exp (Real.log (gamma a)) := (Real.exp_log hp).symm
      _ ≤ _ := Real.exp_le_exp.mpr hh.2

lemma gamma_le_one (a : Fin n → ℝ) (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (ha : ∀ i, |a i| ≤ b) : gamma a ≤ 1 := by
  calc
    _ ≤ Real.exp (-(tau a)) := (gamma_exp_bounds a b hb0 hb1 ha).2
    _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (neg_nonpos.mpr (tau_nonneg a))
    _ = 1 := Real.exp_zero

theorem gamma_linear_lower (a : Fin n → ℝ) (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (ha : ∀ i, |a i| ≤ b) : 1-tau a/(1-b^2) ≤ gamma a := by
  have he := Real.add_one_le_exp (-(tau a)/(1-b^2))
  have hh := (gamma_exp_bounds a b hb0 hb1 ha).1
  simp only [neg_div] at he hh
  linarith

theorem gamma_deficit (a : Fin n → ℝ) (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (ha : ∀ i, |a i| ≤ b) :
    0 ≤ 1-gamma a ∧ 1-gamma a ≤ tau a/(1-b^2) := by
  have hlow := gamma_linear_lower a b hb0 hb1 ha
  have hupp := gamma_le_one a b hb0 hb1 ha
  constructor <;> linarith

/-- Applicable to the normalized scores of any actual unit-score reference.
The hypothesis describes squares, so either choice of sign is allowed. -/
lemma even_reference_abs (hn : 2 ≤ n) (a : Fin n → ℝ)
    (hsq : ∀ i, (a i)^2 = 1/((n:ℝ)-1)^2) (i : Fin n) :
    |a i| = 1/((n:ℝ)-1) := by
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hd : 0 < (n:ℝ)-1 := by linarith
  have hb0 : 0 ≤ 1/((n:ℝ)-1) := div_nonneg (by norm_num) hd.le
  apply (sq_eq_sq₀ (abs_nonneg _) hb0).mp
  simpa only [sq_abs, div_pow, one_pow] using hsq i

lemma even_reference_tau (a : Fin n → ℝ)
    (hsq : ∀ i, (a i)^2 = 1/((n:ℝ)-1)^2) :
    tau a = (n:ℝ)/((n:ℝ)-1)^2 := by
  simp only [tau, hsq, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

lemma even_reference_gamma_exact (a : Fin n → ℝ)
    (hsq : ∀ i, (a i)^2 = 1/((n:ℝ)-1)^2) :
    gamma a = (1-1/((n:ℝ)-1)^2)^n := by
  simp only [gamma, hsq, prod_const, card_univ, Fintype.card_fin]

theorem even_reference_exp_bounds (hn : 3 ≤ n) (a : Fin n → ℝ)
    (hsq : ∀ i, (a i)^2 = 1/((n:ℝ)-1)^2) :
    Real.exp (-1/((n:ℝ)-2)) ≤ gamma a ∧
      gamma a ≤ Real.exp (-(n:ℝ)/((n:ℝ)-1)^2) := by
  have hnR : (3:ℝ) ≤ n := by exact_mod_cast hn
  have hd : 0 < (n:ℝ)-1 := by linarith
  have hd2 : 0 < (n:ℝ)-2 := by linarith
  have hb0 : 0 ≤ 1/((n:ℝ)-1) := by positivity
  have hb1 : 1/((n:ℝ)-1) < 1 := (div_lt_one hd).mpr (by linarith)
  have hcap (i : Fin n) : |a i| ≤ 1/((n:ℝ)-1) :=
    (even_reference_abs (by omega) a hsq i).le
  have hh := gamma_exp_bounds a (1/((n:ℝ)-1)) hb0 hb1 hcap
  rw [even_reference_tau a hsq] at hh
  have hgap := base_denominator_pos hb0 hb1
  have hratio : ((n:ℝ)/((n:ℝ)-1)^2)/(1-(1/((n:ℝ)-1))^2) = 1/((n:ℝ)-2) := by
    apply (div_eq_iff hgap.ne').mpr
    field_simp [hd.ne', hd2.ne']
    ring
  simpa only [neg_div, hratio] using hh

/-- Explicit 1-O(1/n) factor bound, not a path-count lower bound. -/
theorem even_reference_near_one (hn : 4 ≤ n) (a : Fin n → ℝ)
    (hsq : ∀ i, (a i)^2 = 1/((n:ℝ)-1)^2) :
    1-2/(n:ℝ) ≤ gamma a ∧ gamma a ≤ 1 := by
  have hnR : (4:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n:ℝ) := by linarith
  have hd2 : 0 < (n:ℝ)-2 := by linarith
  have hh := even_reference_exp_bounds (by omega) a hsq
  have hratio : 1/((n:ℝ)-2) ≤ 2/(n:ℝ) := by
    apply (div_le_div_iff₀ hd2 hn0).mpr
    linarith
  constructor
  · have he := Real.add_one_le_exp (-1/((n:ℝ)-2))
    simp only [neg_div] at he hh
    linarith
  · calc
      _ ≤ Real.exp (-(n:ℝ)/((n:ℝ)-1)^2) := hh.2
      _ ≤ Real.exp 0 := Real.exp_le_exp.mpr
        (div_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _))
      _ = 1 := Real.exp_zero

lemma actual_unit_score_square (T : Tournament n) (hs : ∀ i, (score T i)^2 = 1)
    (i : Fin n) : (normalizedScore T i)^2 = 1/((n:ℝ)-1)^2 := by
  rw [normalizedScore, div_pow, hs i]

/-- Adapter for a supplied actual unit-score tournament. It does not construct
such a tournament or derive a path-count bound from Gamma. -/
theorem actual_unit_score_gamma (T : Tournament n) (hn : 4 ≤ n)
    (hs : ∀ i, (score T i)^2 = 1) :
    tau (normalizedScore T) = (n:ℝ)/((n:ℝ)-1)^2 ∧
    Real.exp (-1/((n:ℝ)-2)) ≤ gamma (normalizedScore T) ∧
    gamma (normalizedScore T) ≤ Real.exp (-(n:ℝ)/((n:ℝ)-1)^2) ∧
    1-2/(n:ℝ) ≤ gamma (normalizedScore T) ∧ gamma (normalizedScore T) ≤ 1 := by
  have hsq := actual_unit_score_square T hs
  have he := even_reference_exp_bounds (by omega) (normalizedScore T) hsq
  have hl := even_reference_near_one hn (normalizedScore T) hsq
  exact ⟨even_reference_tau (normalizedScore T) hsq, he.1, he.2, hl.1, hl.2⟩

end ActualGammaBoundsCandidate
