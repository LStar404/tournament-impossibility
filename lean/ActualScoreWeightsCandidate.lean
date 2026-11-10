import WeightedQuadraticConvolutionCandidate
import ActualPrincipalBudgetCandidate
set_option autoImplicit false
noncomputable section
namespace ActualScoreWeightsCandidate
open TournamentHamiltonian ActualTournamentPrescalingBounds TournamentPrescalingMassBound
open scoped Classical

def weight {n : ℕ} (T : Tournament n) (x : ℝ) (i : Fin n) : ℝ :=
  Real.exp x * ((1+normalizedScore T i)⁻¹ * (1-normalizedScore T i)⁻¹)
def cap (a0 : ℝ) : ℝ := Real.exp 1 / (1-a0^2)

lemma weight_bounds {n : ℕ} (T : Tournament n) (a0 x : ℝ)
    (h0 : 0 ≤ a0) (h1 : a0 < 1) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (ha : ∀ i, |normalizedScore T i| ≤ a0) :
    ∀ i, 1 ≤ weight T x i ∧ weight T x i ≤ cap a0 := by
  have hd : 0 < 1-a0^2 := by nlinarith
  intro i
  let a := normalizedScore T i
  have haa : -1 < a ∧ a < 1 := by have h := abs_le.mp (ha i); dsimp [a]; constructor <;> linarith
  have hasq : a^2 ≤ a0^2 := by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg a) h0).mpr (ha i)
  have hda : 0 < 1-a^2 := by linarith
  have hp : (1+a)⁻¹*(1-a)⁻¹ = 1/(1-a^2) := by
    have hl : 1+a ≠ 0 := by linarith
    have hr : 1-a ≠ 0 := by linarith
    field_simp [hl,hr,hda.ne']
    ring
  have hp0 : 1 ≤ 1/(1-a^2) := (le_div_iff₀ hda).mpr (by nlinarith [sq_nonneg a])
  have hp1 : 1/(1-a^2) ≤ 1/(1-a0^2) :=
    div_le_div_of_nonneg_left (by norm_num) hd (by linarith)
  change 1 ≤ Real.exp x*((1+a)⁻¹*(1-a)⁻¹) ∧
    Real.exp x*((1+a)⁻¹*(1-a)⁻¹) ≤ Real.exp 1/(1-a0^2)
  rw [hp]
  constructor
  · simpa only [one_mul] using mul_le_mul (Real.one_le_exp_iff.mpr hx0) hp0
      (by norm_num : (0 : ℝ) ≤ 1) (Real.exp_nonneg x)
  · have h := mul_le_mul (Real.exp_le_exp.mpr hx1) hp1 (by positivity) (Real.exp_nonneg 1)
    simpa only [mul_one_div] using h

lemma weight_excess {n : ℕ} (T : Tournament n) (hn : 0 < n) (a0 x : ℝ)
    (h0 : 0 ≤ a0) (h1 : a0 < 1) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (ha : ∀ i, |normalizedScore T i| ≤ a0) :
    (∑ i, (weight T x i-1))/n ≤
      Real.exp 1*(tau (normalizedScore T)/((1-a0^2)*n)+x) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hd : 0 < 1-a0^2 := by nlinarith
  have hinc : Real.exp x-1 ≤ Real.exp 1*x := by
    have hh := (exp_sub_one_le_self_mul_exp x).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hx1) hx0)
    simpa only [mul_comm] using hh
  have hlocal (i : Fin n) : weight T x i-1 ≤
      Real.exp 1*((normalizedScore T i)^2/(1-a0^2))+Real.exp 1*x := by
    let a := normalizedScore T i
    have haa : -1 < a ∧ a < 1 := by have h := abs_le.mp (ha i); dsimp [a]; constructor <;> linarith
    have hasq : a^2 ≤ a0^2 := by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg a) h0).mpr (ha i)
    have hda : 0 < 1-a^2 := by linarith
    have hl : 1+a ≠ 0 := by linarith
    have hr : 1-a ≠ 0 := by linarith
    have hid : weight T x i-1 = Real.exp x*(a^2/(1-a^2))+(Real.exp x-1) := by
      unfold weight
      change Real.exp x*((1+a)⁻¹*(1-a)⁻¹)-1 = _
      field_simp [hl,hr,hda.ne']
      ring
    have hfrac : a^2/(1-a^2) ≤ a^2/(1-a0^2) :=
      div_le_div_of_nonneg_left (sq_nonneg a) hd (by linarith)
    have hh := mul_le_mul (Real.exp_le_exp.mpr hx1) hfrac
      (div_nonneg (sq_nonneg a) hda.le) (Real.exp_nonneg 1)
    rw [hid]
    exact add_le_add hh hinc
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hlocal i)
  have hh := div_le_div_of_nonneg_right hs hn0.le
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
  apply hh.trans_eq
  unfold tau
  field_simp

lemma weight_prod {n : ℕ} (T : Tournament n) (x : ℝ) (U : Finset (Fin n)) :
    (∏ i ∈ U, weight T x i) = Real.exp ((U.card : ℝ)*x)*
      (∏ i ∈ U, (1+normalizedScore T i)⁻¹)*(∏ j ∈ U, (1-normalizedScore T j)⁻¹) := by
  simp only [weight,Finset.prod_mul_distrib,Finset.prod_const]
  rw [← Real.exp_nat_mul]
  ring

end ActualScoreWeightsCandidate

set_option pp.fullNames true
#check ActualScoreWeightsCandidate.weight
#print axioms ActualScoreWeightsCandidate.weight
#check ActualScoreWeightsCandidate.cap
#print axioms ActualScoreWeightsCandidate.cap
#check ActualScoreWeightsCandidate.weight_bounds
#print axioms ActualScoreWeightsCandidate.weight_bounds
#check ActualScoreWeightsCandidate.weight_excess
#print axioms ActualScoreWeightsCandidate.weight_excess
#check ActualScoreWeightsCandidate.weight_prod
#print axioms ActualScoreWeightsCandidate.weight_prod
