import TournamentPrescalingMass

/-!
Quantitative G1 prescaling mass bound, derived from actual scores and bounded
entries. No small-mass or source-norm conclusion is assumed. Focused Lean checks are recorded alongside this file. This module does not
assert the global extremal entry theorem.
-/
noncomputable section
namespace TournamentPrescalingMassBound
open Finset TournamentPrescalingMass
variable {n : ℕ}

def tau (a : Fin n → ℝ) : ℝ := ∑ i, (a i)^2

def radiusFactor (a0 : ℝ) : ℝ := (1 - a0^2)⁻¹

def errorScale (n : ℕ) (t : ℝ) : ℝ :=
  (t + t^2) / n + t * Real.sqrt t / Real.sqrt (n : ℝ)

lemma tau_nonneg (a : Fin n → ℝ) : 0 ≤ tau a :=
  sum_nonneg (fun _ _ => sq_nonneg _)

lemma base_denominator_pos {a0 : ℝ} (h0 : 0 ≤ a0) (h1 : a0 < 1) :
    0 < 1 - a0^2 := by
  apply sub_pos.mpr
  exact (sq_lt_one_iff_abs_lt_one a0).mpr (by simpa [abs_of_nonneg h0] using h1)

lemma radiusFactor_pos {a0 : ℝ} (h0 : 0 ≤ a0) (h1 : a0 < 1) :
    0 < radiusFactor a0 := inv_pos.mpr (base_denominator_pos h0 h1)

lemma one_le_radiusFactor {a0 : ℝ} (h0 : 0 ≤ a0) (h1 : a0 < 1) :
    1 ≤ radiusFactor a0 :=
  (one_le_inv₀ (base_denominator_pos h0 h1)).mpr (by nlinarith [sq_nonneg a0])

lemma coordinate_sq_le {a0 x : ℝ} (_h0 : 0 ≤ a0) (hx : |x| ≤ a0) :
    x^2 ≤ a0^2 := by
  simpa [← pow_two, sq_abs] using mul_self_le_mul_self (abs_nonneg x) hx

lemma coordinate_denominator_pos {a0 x : ℝ}
    (h0 : 0 ≤ a0) (h1 : a0 < 1) (hx : |x| ≤ a0) : 0 < 1 - x^2 := by
  have hb := base_denominator_pos h0 h1
  have hs := coordinate_sq_le h0 hx
  linarith

lemma inverse_denominator_le {a0 x : ℝ}
    (h0 : 0 ≤ a0) (h1 : a0 < 1) (hx : |x| ≤ a0) :
    (1 - x^2)⁻¹ ≤ radiusFactor a0 := by
  apply (inv_le_inv₀ (coordinate_denominator_pos h0 h1 hx)
    (base_denominator_pos h0 h1)).mpr
  linarith [coordinate_sq_le h0 hx]

lemma w_nonneg (a : Fin n → ℝ) {a0 : ℝ}
    (h0 : 0 ≤ a0) (h1 : a0 < 1) (ha : ∀ i, |a i| ≤ a0) (i : Fin n) :
    0 ≤ w a i :=
  div_nonneg (sq_nonneg _) (coordinate_denominator_pos h0 h1 (ha i)).le

lemma w_le (a : Fin n → ℝ) {a0 : ℝ}
    (h0 : 0 ≤ a0) (h1 : a0 < 1) (ha : ∀ i, |a i| ≤ a0) (i : Fin n) :
    w a i ≤ radiusFactor a0 * (a i)^2 := by
  simpa [w, div_eq_mul_inv, mul_comm] using
    mul_le_mul_of_nonneg_left (inverse_denominator_le h0 h1 (ha i)) (sq_nonneg (a i))

lemma abs_v_le (a : Fin n → ℝ) {a0 : ℝ}
    (h0 : 0 ≤ a0) (h1 : a0 < 1) (ha : ∀ i, |a i| ≤ a0) (i : Fin n) :
    |v a i| ≤ radiusFactor a0 * |a i| := by
  rw [v, abs_div, abs_of_pos (coordinate_denominator_pos h0 h1 (ha i)), div_eq_mul_inv]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left
    (inverse_denominator_le h0 h1 (ha i)) (abs_nonneg (a i))

lemma sum_w_bounds (a : Fin n → ℝ) {a0 : ℝ}
    (h0 : 0 ≤ a0) (h1 : a0 < 1) (ha : ∀ i, |a i| ≤ a0) :
    0 ≤ (∑ i, w a i) ∧ (∑ i, w a i) ≤ radiusFactor a0 * tau a := by
  constructor
  · exact sum_nonneg (fun i _ => w_nonneg a h0 h1 ha i)
  · simpa [tau, ← mul_sum] using sum_le_sum (fun i _ => w_le a h0 h1 ha i)

lemma sum_v_sq_le (a : Fin n → ℝ) {a0 : ℝ}
    (h0 : 0 ≤ a0) (h1 : a0 < 1) (ha : ∀ i, |a i| ≤ a0) :
    (∑ i, (v a i)^2) ≤ (radiusFactor a0)^2 * tau a := by
  calc
    _ ≤ ∑ i, (radiusFactor a0)^2 * (a i)^2 := by
      apply sum_le_sum
      intro i hi
      have hs := mul_self_le_mul_self (abs_nonneg (v a i)) (abs_v_le a h0 h1 ha i)
      simpa [← pow_two, mul_pow, sq_abs] using hs
    _ = _ := by rw [← mul_sum]; rfl

lemma sqrt_sum_v_sq_le (a : Fin n → ℝ) {a0 : ℝ}
    (h0 : 0 ≤ a0) (h1 : a0 < 1) (ha : ∀ i, |a i| ≤ a0) :
    Real.sqrt (∑ i, (v a i)^2) ≤ radiusFactor a0 * Real.sqrt (tau a) := by
  apply (Real.sqrt_le_left (mul_nonneg (radiusFactor_pos h0 h1).le (Real.sqrt_nonneg _))).mpr
  rw [mul_pow, Real.sq_sqrt (tau_nonneg a)]
  exact sum_v_sq_le a h0 h1 ha

lemma sum_abs_v_le (a : Fin n → ℝ) {a0 : ℝ}
    (h0 : 0 ≤ a0) (h1 : a0 < 1) (ha : ∀ i, |a i| ≤ a0) :
    (∑ i, |v a i|) ≤ radiusFactor a0 * Real.sqrt (n : ℝ) * Real.sqrt (tau a) := by
  have hc := Real.sum_mul_le_sqrt_mul_sqrt (univ : Finset (Fin n))
    (fun _ => (1 : ℝ)) (fun i => |v a i|)
  simp only [one_mul, one_pow, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, sq_abs] at hc
  calc
    _ ≤ Real.sqrt (n : ℝ) * Real.sqrt (∑ i, (v a i)^2) := hc
    _ ≤ Real.sqrt (n : ℝ) * (radiusFactor a0 * Real.sqrt (tau a)) :=
      mul_le_mul_of_nonneg_left (sqrt_sum_v_sq_le a h0 h1 ha) (Real.sqrt_nonneg _)
    _ = _ := by ring

/-- The exact cubic remainder, needed to avoid a spurious sqrt(n*tau) bound on V. -/
lemma v_eq_a_add_aw (a : Fin n → ℝ) {a0 : ℝ}
    (h0 : 0 ≤ a0) (h1 : a0 < 1) (ha : ∀ i, |a i| ≤ a0) (i : Fin n) :
    v a i = a i + a i * w a i := by
  have hd := (coordinate_denominator_pos h0 h1 (ha i)).ne'
  dsimp [v, w]
  field_simp [hd]; ring

lemma abs_sum_v_le (a : Fin n → ℝ) {a0 : ℝ}
    (h0 : 0 ≤ a0) (h1 : a0 < 1) (ha : ∀ i, |a i| ≤ a0)
    (hsum : ∑ i, a i = 0) :
    |∑ i, v a i| ≤ radiusFactor a0 * tau a := by
  have he : (∑ i, v a i) = ∑ i, a i * w a i := by
    simp_rw [v_eq_a_add_aw a h0 h1 ha]
    rw [sum_add_distrib, hsum, zero_add]
  rw [he]
  calc
    _ ≤ ∑ i, |a i * w a i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, w a i := by
      apply sum_le_sum
      intro i hi
      rw [abs_mul, abs_of_nonneg (w_nonneg a h0 h1 ha i)]
      simpa using mul_le_mul_of_nonneg_right ((ha i).trans h1.le) (w_nonneg a h0 h1 ha i)
    _ ≤ _ := (sum_w_bounds a h0 h1 ha).2

lemma zero_total_score (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : ∀ i j, S i j = -S j i) (a : Fin n → ℝ)
    (hn : (n : ℝ) - 1 ≠ 0)
    (hscore : ∀ i, ∑ j, S i j = ((n : ℝ) - 1) * a i) :
    ∑ i, a i = 0 := by
  have ht : (∑ i, ∑ j, S i j) = 0 := by
    simpa [bilinear] using bilinear_self_zero S hS (fun _ => 1)
  simp_rw [hscore] at ht
  rw [← mul_sum] at ht
  exact (mul_eq_zero.mp ht).resolve_left hn

lemma row_v_abs_le (S : Matrix (Fin n) (Fin n) ℝ)
    (hentry : ∀ i j, |S i j| ≤ 1) (a : Fin n → ℝ) {a0 : ℝ}
    (h0 : 0 ≤ a0) (h1 : a0 < 1) (ha : ∀ i, |a i| ≤ a0) (i : Fin n) :
    |∑ j, S i j * v a j| ≤
      radiusFactor a0 * Real.sqrt (n : ℝ) * Real.sqrt (tau a) := by
  calc
    _ ≤ ∑ j, |S i j * v a j| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |v a j| := by
      apply sum_le_sum
      intro j hj
      rw [abs_mul]
      simpa using mul_le_mul_of_nonneg_right (hentry i j) (abs_nonneg (v a j))
    _ ≤ _ := sum_abs_v_le a h0 h1 ha

/-- A genuine finite estimate for the ordered cross term w^T S v. -/
theorem cross_term_bound (S : Matrix (Fin n) (Fin n) ℝ)
    (hentry : ∀ i j, |S i j| ≤ 1) (a : Fin n → ℝ) {a0 : ℝ}
    (h0 : 0 ≤ a0) (h1 : a0 < 1) (ha : ∀ i, |a i| ≤ a0) :
    |bilinear S (w a) (v a)| ≤
      (radiusFactor a0)^2 * Real.sqrt (n : ℝ) * tau a * Real.sqrt (tau a) := by
  have he : bilinear S (w a) (v a) = ∑ i, w a i * (∑ j, S i j * v a j) := by
    simp [bilinear, mul_sum, mul_assoc]
  rw [he]
  calc
    _ ≤ ∑ i, |w a i * (∑ j, S i j * v a j)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, w a i * (radiusFactor a0 * Real.sqrt (n : ℝ) * Real.sqrt (tau a)) := by
      apply sum_le_sum
      intro i hi
      rw [abs_mul, abs_of_nonneg (w_nonneg a h0 h1 ha i)]
      exact mul_le_mul_of_nonneg_left (row_v_abs_le S hentry a h0 h1 ha i)
        (w_nonneg a h0 h1 ha i)
    _ = (∑ i, w a i) * (radiusFactor a0 * Real.sqrt (n : ℝ) * Real.sqrt (tau a)) :=
      (sum_mul _ _ _).symm
    _ ≤ (radiusFactor a0 * tau a) *
        (radiusFactor a0 * Real.sqrt (n : ℝ) * Real.sqrt (tau a)) :=
      mul_le_mul_of_nonneg_right (sum_w_bounds a h0 h1 ha).2 (by
        exact mul_nonneg (mul_nonneg (radiusFactor_pos h0 h1).le (Real.sqrt_nonneg _))
          (Real.sqrt_nonneg _))
    _ = _ := by ring

lemma numerator_bound (S : Matrix (Fin n) (Fin n) ℝ)
    (hentry : ∀ i j, |S i j| ≤ 1) (a : Fin n → ℝ) {a0 : ℝ}
    (h0 : 0 ≤ a0) (h1 : a0 < 1) (ha : ∀ i, |a i| ≤ a0)
    (hsum : ∑ i, a i = 0) :
    |(∑ i, w a i)^2 - (∑ i, v a i)^2 + (∑ i, w a i) +
      2 * bilinear S (w a) (v a)| ≤
        radiusFactor a0 * tau a + 2 * (radiusFactor a0)^2 * (tau a)^2 +
        2 * (radiusFactor a0)^2 * Real.sqrt (n : ℝ) * tau a * Real.sqrt (tau a) := by
  have hw := sum_w_bounds a h0 h1 ha
  have hv := abs_sum_v_le a h0 h1 ha hsum
  have hws := mul_self_le_mul_self hw.1 hw.2
  have hvs := mul_self_le_mul_self (abs_nonneg (∑ i, v a i)) hv
  simp only [← pow_two, mul_pow, sq_abs] at hws hvs
  have hc := cross_term_bound S hentry a h0 h1 ha
  have hA := abs_sub ((∑ i, w a i)^2) ((∑ i, v a i)^2)
  rw [abs_of_nonneg (sq_nonneg (∑ i, w a i)),
    abs_of_nonneg (sq_nonneg (∑ i, v a i))] at hA
  have hB := abs_add_le ((∑ i, w a i)^2 - (∑ i, v a i)^2) (∑ i, w a i)
  rw [abs_of_nonneg hw.1] at hB
  have hC := abs_add_le ((∑ i, w a i)^2 - (∑ i, v a i)^2 + (∑ i, w a i))
    (2 * bilinear S (w a) (v a))
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hC
  nlinarith

/-- The exact-denominator quantitative bound, before n-1 is replaced by n/2. -/
theorem massExcess_bound_exact (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : ∀ i j, S i j = -S j i) (hentry : ∀ i j, |S i j| ≤ 1)
    (a : Fin n → ℝ) (hn : 2 ≤ n) {a0 : ℝ}
    (h0 : 0 ≤ a0) (h1 : a0 < 1) (ha : ∀ i, |a i| ≤ a0)
    (hscore : ∀ i, ∑ j, S i j = ((n : ℝ) - 1) * a i) :
    |massExcess S a| ≤
      (radiusFactor a0 * tau a + 2 * (radiusFactor a0)^2 * (tau a)^2 +
        2 * (radiusFactor a0)^2 * Real.sqrt (n : ℝ) * tau a * Real.sqrt (tau a)) /
          ((n : ℝ) - 1) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 < (n : ℝ) - 1 := by linarith
  rw [massExcess_identity S hS a (fun i => (ha i).trans_lt h1) hp.ne' hscore,
    abs_div, abs_of_pos hp]
  exact div_le_div_of_nonneg_right
    (numerator_bound S hentry a h0 h1 ha (zero_total_score S hS a hp.ne' hscore)) hp.le

lemma denominator_comparison {b t : ℝ} (hb : 1 ≤ b) (ht : 0 ≤ t) (hn : 2 ≤ n) :
    (b*t + 2*b^2*t^2 + 2*b^2*Real.sqrt (n : ℝ)*t*Real.sqrt t) / ((n : ℝ)-1) ≤
      4*b^2 * errorScale n t := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by linarith
  have hnm : 0 < (n : ℝ)-1 := by linarith
  have hb0 : 0 ≤ b := by linarith
  let N := b*t + 2*b^2*t^2 + 2*b^2*Real.sqrt (n : ℝ)*t*Real.sqrt t
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hhalf : N / ((n : ℝ)-1) ≤ (2*N)/(n : ℝ) := by
    apply (div_le_div_iff₀ hnm hn0).mpr
    nlinarith [mul_nonneg hN (show 0 ≤ (n : ℝ)-2 by linarith)]
  have hb2 : b ≤ 2*b^2 := by nlinarith
  have hnum : 2*b*t + 4*b^2*t^2 ≤ 4*b^2*(t+t^2) := by
    nlinarith [mul_le_mul_of_nonneg_right hb2 ht]
  calc
    _ ≤ (2*N)/(n : ℝ) := hhalf
    _ = (2*b*t+4*b^2*t^2)/(n : ℝ) +
        (4*b^2*t*Real.sqrt t) * (Real.sqrt (n : ℝ)/(n : ℝ)) := by dsimp [N]; ring
    _ = (2*b*t+4*b^2*t^2)/(n : ℝ) +
        4*b^2*t*Real.sqrt t / Real.sqrt (n : ℝ) := by rw [Real.sqrt_div_self']; ring
    _ ≤ (4*b^2*(t+t^2))/(n : ℝ) +
        4*b^2*t*Real.sqrt t / Real.sqrt (n : ℝ) :=
      add_le_add (div_le_div_of_nonneg_right hnum hn0.le) le_rfl
    _ = _ := by unfold errorScale; ring

/-- G1's explicit mass-error estimate. Constants depend only on the fixed
coordinate-score cap a0; tau need not be bounded or O(1/n). -/
theorem massExcess_bound (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : ∀ i j, S i j = -S j i) (hentry : ∀ i j, |S i j| ≤ 1)
    (a : Fin n → ℝ) (hn : 2 ≤ n) {a0 : ℝ}
    (h0 : 0 ≤ a0) (h1 : a0 < 1) (ha : ∀ i, |a i| ≤ a0)
    (hscore : ∀ i, ∑ j, S i j = ((n : ℝ) - 1) * a i) :
    |massExcess S a| ≤ 4 * (radiusFactor a0)^2 * errorScale n (tau a) :=
  (massExcess_bound_exact S hS hentry a hn h0 h1 ha hscore).trans
    (denominator_comparison (one_le_radiusFactor h0 h1) (tau_nonneg a) hn)

/-- The parameter tau is literally the actual squared score energy divided by
(n-1)^2, including Lean's totalized division convention at n=1. -/
theorem actual_tau_identity (T : TournamentHamiltonian.Tournament n) :
    tau (fun i => TournamentHamiltonian.score T i / ((n : ℝ)-1)) =
      ActualTournamentDeletionEnergy.fullEnergy T / ((n : ℝ)-1)^2 := by
  simp [tau, div_pow, ActualTournamentDeletionEnergy.fullEnergy, sum_div]

/-- The quantitative bound for the same tournament whose actual paths are counted. -/
theorem actual_tournament_massExcess_bound (T : TournamentHamiltonian.Tournament n)
    (hn : 2 ≤ n) {a0 : ℝ} (h0 : 0 ≤ a0) (h1 : a0 < 1)
    (ha : ∀ i, |TournamentHamiltonian.score T i / ((n : ℝ)-1)| ≤ a0) :
    |massExcess (TournamentHamiltonian.signMatrix T)
        (fun i => TournamentHamiltonian.score T i / ((n : ℝ)-1))| ≤
      4 * (radiusFactor a0)^2 * errorScale n
        (ActualTournamentDeletionEnergy.fullEnergy T / ((n : ℝ)-1)^2) := by
  rw [← actual_tau_identity]
  apply massExcess_bound _ (TournamentHamiltonian.signMatrix_skew T)
    (ActualTournamentDeletionEnergy.sign_abs_le_one T) _ hn h0 h1 ha
  intro i
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hne : (n : ℝ)-1 ≠ 0 := by linarith
  change TournamentHamiltonian.score T i =
    ((n : ℝ)-1) * (TournamentHamiltonian.score T i / ((n : ℝ)-1))
  field_simp [hne]

end TournamentPrescalingMassBound
#print axioms TournamentPrescalingMassBound.cross_term_bound
#print axioms TournamentPrescalingMassBound.massExcess_bound_exact
#print axioms TournamentPrescalingMassBound.massExcess_bound
#print axioms TournamentPrescalingMassBound.actual_tournament_massExcess_bound

#print axioms TournamentPrescalingMassBound.actual_tau_identity
