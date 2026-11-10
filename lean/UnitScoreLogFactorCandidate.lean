import UnitScoreEnvelopesCandidate
set_option autoImplicit false
noncomputable section
namespace UnitScoreLogFactorCandidate
open Finset TournamentHamiltonian ActualTournamentPrescalingBounds ActualPrescalingNormalization
open TournamentPrescalingMassBound UnitScorePrefactorCandidate UnitScoreEnvelopesCandidate
open PhysicalMinorRecoveryCandidate
variable {n m : ℕ}

lemma retained_log_bound (T : Tournament n) (hn : 4≤n)
    (hs : ∀ i, |score T i|≤1) (I : Finset (Fin n)) :
    0<(∏ i∈Iᶜ,(1-(normalizedScore T i)^2)) ∧
    |Real.log (∏ i∈Iᶜ,(1-(normalizedScore T i)^2))|≤6/(n:ℝ) := by
  have hc := unit_score_caps T hn hs
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hf (i) : 0<1-(normalizedScore T i)^2 :=
    coordinate_denominator_pos (by norm_num : (0:ℝ)≤1/2) (by norm_num) (hc.2.1 i)
  refine ⟨Finset.prod_pos (fun i hi => hf i),?_⟩
  rw [Real.log_prod (fun i hi => (hf i).ne')]
  have hl : ∀ i, -(4/3)*(normalizedScore T i)^2≤Real.log (1-(normalizedScore T i)^2) ∧
      Real.log (1-(normalizedScore T i)^2)≤0 := by
    intro i
    have hh := ActualGammaBoundsCandidate.factor_log_bounds (normalizedScore T i) (1/2)
      (by norm_num) (by norm_num) (hc.2.1 i)
    norm_num at hh
    constructor
    · nlinarith [hh.1]
    · linarith [hh.2, sq_nonneg (normalizedScore T i)]
  have hsum : (∑ i∈Iᶜ,(normalizedScore T i)^2)≤tau (normalizedScore T) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i hi hj => sq_nonneg _)
  have hlo := Finset.sum_le_sum (s:=Iᶜ) (fun i hi => (hl i).1)
  have hhi := Finset.sum_nonpos (s:=Iᶜ) (fun i hi => (hl i).2)
  rw [← Finset.mul_sum] at hlo
  rw [abs_of_nonpos hhi]
  have ht := hc.2.2.1
  simp only [div_eq_mul_inv] at ht ⊢
  nlinarith [inv_nonneg.mpr hnR.le]

lemma normalization_log_bound (T : Tournament n) (hn : 16≤n)
    (hs : ∀ i, |score T i|≤1) (hm : m≤n) :
    0<1+nu T/(n:ℝ) ∧ |(m:ℝ)*Real.log (1+nu T/(n:ℝ))|≤64/(n:ℝ) := by
  have hn4 : 4≤n := by omega
  have hnR : (16:ℝ)≤n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by linarith
  have hnu := (nu_abs_bound T (by omega) (by norm_num : (0:ℝ)≤1/2) (by norm_num)
    (unit_score_caps T hn4 hs).2.1).trans (unit_mass_delta T hn4 hs).1
  have hratio : |nu T/(n:ℝ)|≤1/2 := by
    rw [abs_div, abs_of_pos hn0]
    apply (div_le_iff₀ hn0).mpr
    apply hnu.trans
    apply (div_le_iff₀ hn0).mpr
    nlinarith
  have hp : 0<1+nu T/(n:ℝ) := by linarith [(abs_le.mp hratio).1]
  refine ⟨hp,?_⟩
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg m)]
  have hl := mul_le_mul_of_nonneg_left (log_one_add_abs hratio) (Nat.cast_nonneg m)
  rw [abs_div, abs_of_pos hn0] at hl
  have hmR : (m:ℝ)≤n := by exact_mod_cast hm
  have hh : (m:ℝ)*(|nu T|/(n:ℝ))≤|nu T| := by
    calc
      _ ≤ (n:ℝ)*(|nu T|/(n:ℝ)) := mul_le_mul_of_nonneg_right hmR (by positivity)
      _ = _ := by field_simp
  have hnu2 := mul_le_mul_of_nonneg_left hnu (by norm_num : (0:ℝ)≤2)
  simp only [div_eq_mul_inv] at hl hnu2 hh ⊢
  nlinarith

lemma full_log_bound (T : Tournament n) (hn : 16≤n)
    (hs : ∀ i, |score T i|≤1) (I : Finset (Fin n)) (x y : Fin m → ℝ)
    (hm : m≤n) :
    0<fullPrefactor T I x y ∧
    |Real.log (fullPrefactor T I x y)|≤70/(n:ℝ)+|shiftedPotential T I I x y| := by
  have hG := retained_log_bound T (by omega) hs I
  have hN := normalization_log_bound T hn hs hm
  have hp : 0<(1+nu T/(n:ℝ))^m := pow_pos hN.1 _
  refine ⟨mul_pos (mul_pos hG.1 hp) (Real.exp_pos _),?_⟩
  unfold fullPrefactor
  rw [Real.log_mul (mul_pos hG.1 hp).ne' (Real.exp_pos _).ne',
    Real.log_mul hG.1.ne' hp.ne', Real.log_pow, Real.log_exp]
  calc
    _ ≤ |Real.log (∏ i∈Iᶜ,(1-(normalizedScore T i)^2))+(m:ℝ)*Real.log (1+nu T/(n:ℝ))|+
        |-(shiftedPotential T I I x y)| := abs_add_le _ _
    _ ≤ (6/(n:ℝ)+64/(n:ℝ))+|shiftedPotential T I I x y| := by
      rw [abs_neg]
      exact add_le_add ((abs_add_le _ _).trans (add_le_add hG.2 hN.2)) le_rfl
    _ = _ := by ring
end UnitScoreLogFactorCandidate
