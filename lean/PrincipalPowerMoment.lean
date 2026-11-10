import TournamentHamiltonian.NormalizedConvolution

namespace TournamentHamiltonian
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

theorem weighted_principal_powerMoment_le {n : ℕ} (T : Tournament n) (hn : 0 < n)
    (r : ℕ) (w : Fin n → ℝ) (W : ℝ) (hW : 0 ≤ W)
    (hw0 : ∀ i, 0 ≤ w i) (hwW : ∀ i, w i ≤ W) :
    (∑ U : Finset (Fin n), (2 / (n : ℝ)) ^ U.card * (principalWeightMatrix T U).det *
      (U.card : ℝ) ^ r * ∏ i ∈ U, w i) ≤ ∑' k, subsetMoment W r k := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hloc (k : ℕ) (U : Finset (Fin n)) (hU : U ∈ (Finset.univ : Finset (Fin n)).powersetCard k) :
      (2 / (n : ℝ)) ^ U.card * (principalWeightMatrix T U).det * (U.card : ℝ) ^ r * ∏ i ∈ U, w i ≤
        (2 / (n : ℝ)) ^ k * (((k : ℝ) + 1) / 2) ^ ((k : ℝ) / 2) * (k : ℝ) ^ r * W ^ k := by
    have hc := (Finset.mem_powersetCard.mp hU).2
    have hp : (∏ i ∈ U, w i) ≤ W ^ k := by
      have h := Finset.prod_le_prod₀ (s := U) (fun i _ => hw0 i) (fun i _ => hwW i)
      simpa only [Finset.prod_const, hc] using h
    have hd := principal_weight_le_rpow T U
    rw [hc] at hd ⊢
    apply mul_le_mul _ hp (Finset.prod_nonneg (fun i _ => hw0 i)) (by positivity)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd (by positivity)) (by positivity)
  have hcard (k : ℕ) :
      (∑ U ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        (2 / (n : ℝ)) ^ U.card * (principalWeightMatrix T U).det * (U.card : ℝ) ^ r * ∏ i ∈ U, w i) ≤
        subsetMoment W r k := by
    calc
      _ ≤ ∑ _U ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
          (2 / (n : ℝ)) ^ k * (((k : ℝ) + 1) / 2) ^ ((k : ℝ) / 2) * (k : ℝ) ^ r * W ^ k :=
        Finset.sum_le_sum (fun U hU => hloc k U hU)
      _ = (n.choose k : ℝ) * ((2 / (n : ℝ)) ^ k * (((k : ℝ) + 1) / 2) ^ ((k : ℝ) / 2) *
          (k : ℝ) ^ r * W ^ k) := by simp
      _ ≤ ((n : ℝ) ^ k / k.factorial) * ((2 / (n : ℝ)) ^ k *
          (((k : ℝ) + 1) / 2) ^ ((k : ℝ) / 2) * (k : ℝ) ^ r * W ^ k) :=
        mul_le_mul_of_nonneg_right (Nat.choose_le_pow_div k n) (by positivity)
      _ = subsetMoment W r k := by rw [subsetMoment, subsetWeight_eq, div_pow]; field_simp
  rw [sum_finsets_by_card]
  apply (Finset.sum_le_sum (fun k _ => hcard k)).trans
  exact (subsetMoment_summable hW r).sum_le_tsum _ (fun k _ => subsetMoment_nonneg hW r k)

end TournamentHamiltonian

namespace TournamentHamiltonian
end TournamentHamiltonian
