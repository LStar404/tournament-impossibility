import ExceptionalGeneratingCandidate
import ExceptionalDeletionCandidate
import MeetingConvolutionFinite
import CrudeSkewDetBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace TournamentHamiltonian
open scoped Classical Topology
open Filter

theorem disjointShortConvolution_le_generating {n : ℕ} (T : Tournament n) (F : Finset (Fin n))
    (K : ℕ) (hn : 0 < n) (hK : 2 * K ≤ n) (Q : ℝ) (hQ : 0 ≤ Q)
    (hper : ∀ U : Finset (Fin n), U.card < K → Disjoint U F →
      ((adjacency T).submatrix (Subtype.val : (Uᶜ : Finset (Fin n)) → Fin n) Subtype.val).permanent ≤
        Q * (((n - U.card).factorial : ℝ) / (2 : ℝ) ^ (n - U.card))) :
    disjointShortConvolution T F K / meanPaths n ≤
      (Q / 2) * Real.exp (2 * (K : ℝ) ^ 2 / n) *
        ∑ U ∈ Fᶜ.powerset, (2 / (n : ℝ)) ^ U.card * (principalWeightMatrix T U).det := by
  let Z : ℝ := (n.factorial : ℝ) / (2 : ℝ) ^ n
  have hZ : 0 < Z := by dsimp [Z]; positivity
  have hm : 0 < meanPaths n := by unfold meanPaths; positivity
  have hmZ : meanPaths n = 2 * Z := by
    dsimp [Z]
    simpa only [mul_div_assoc] using meanPaths_eq_twice_normalization n (by omega)
  have hsum : Fᶜ.powerset = (Finset.univ : Finset (Finset (Fin n))).filter (fun U => U ⊆ Fᶜ) := by
    ext U; simp
  rw [disjointShortConvolution, Finset.sum_div, Finset.mul_sum, hsum, Finset.sum_filter]
  apply Finset.sum_le_sum
  intro U _
  have hdet : 0 ≤ (principalWeightMatrix T U).det := (principal_weight_pos T U).le
  by_cases hshort : U.card < K ∧ Disjoint U F
  · have hsub : U ⊆ Fᶜ := by
      intro x hx
      exact Finset.mem_compl.mpr (fun hf => Finset.disjoint_left.mp hshort.2 hx hf)
    simp only [hshort, hsub, ite_true]
    have hkK : (U.card : ℝ) ≤ K := by exact_mod_cast hshort.1.le
    have hkN : 2 * U.card ≤ n := by omega
    have hf := convolution_factorial_ratio_le n U.card hn hkN
    have hexp : Real.exp (2 * (U.card : ℝ) ^ 2 / n) ≤ Real.exp (2 * (K : ℝ) ^ 2 / n) := by
      apply Real.exp_le_exp.mpr
      apply div_le_div_of_nonneg_right _ (by positivity : 0 ≤ (n : ℝ))
      nlinarith [show (0 : ℝ) ≤ U.card by positivity]
    have hf' := hf.trans (mul_le_mul_of_nonneg_right hexp (by positivity : 0 ≤ (2 / (n : ℝ)) ^ U.card))
    calc
      convolutionTerm T U / meanPaths n ≤
          (Q * (((n - U.card).factorial : ℝ) / (2 : ℝ) ^ (n - U.card))) * (principalWeightMatrix T U).det / meanPaths n := by
        apply div_le_div_of_nonneg_right _ hm.le
        unfold convolutionTerm
        have h := mul_le_mul_of_nonneg_right (hper U hshort.1 hshort.2) hdet
        simpa only [mul_comm] using h
      _ = (Q / 2 * (principalWeightMatrix T U).det) *
          ((((n - U.card).factorial : ℝ) / (2 : ℝ) ^ (n - U.card)) / Z) := by
        rw [hmZ]
        ring
      _ ≤ (Q / 2 * (principalWeightMatrix T U).det) *
          (Real.exp (2 * (K : ℝ) ^ 2 / n) * (2 / (n : ℝ)) ^ U.card) :=
        mul_le_mul_of_nonneg_left hf' (mul_nonneg (by positivity) hdet)
      _ = _ := by ring
  · simp only [hshort, ite_false, zero_div]
    split_ifs <;> positivity

theorem disjointShortConvolution_le_core_det {n : ℕ} (T : Tournament n) (F : Finset (Fin n))
    (K : ℕ) (hn : 0 < n) (hK : 2 * K ≤ n) (Q : ℝ) (hQ : 0 ≤ Q)
    (hper : ∀ U : Finset (Fin n), U.card < K → Disjoint U F →
      ((adjacency T).submatrix (Subtype.val : (Uᶜ : Finset (Fin n)) → Fin n) Subtype.val).permanent ≤
        Q * (((n - U.card).factorial : ℝ) / (2 : ℝ) ^ (n - U.card))) :
    disjointShortConvolution T F K / meanPaths n ≤
      Q * Real.exp 1 * Real.exp (2 * (K : ℝ) ^ 2 / n) *
        ((1 : Matrix (Fin Fᶜ.card) (Fin Fᶜ.card) ℝ) +
          (1 / (Fᶜ.card : ℝ)) • signMatrix (inducedTournament T Fᶜ)).det := by
  apply (disjointShortConvolution_le_generating T F K hn hK Q hQ hper).trans
  have h := mul_le_mul_of_nonneg_left (core_principalWeight_generating_le T Fᶜ hn)
    (by positivity : 0 ≤ (Q / 2) * Real.exp (2 * (K : ℝ) ^ 2 / n))
  convert h using 1
  ring


theorem exp_half_lt_five_thirds : Real.exp (1 / 2 : ℝ) < 5 / 3 := by
  have heq : Real.exp (1 / 2 : ℝ) ^ 2 = Real.exp 1 := by
    rw [pow_two, ← Real.exp_add]
    norm_num
  nlinarith [Real.exp_one_lt_d9, Real.exp_pos (1 / 2 : ℝ)]

theorem tournament_skew_kernel_det_lt_five_thirds {n : ℕ} (T : Tournament n) (hn : 0 < n) :
    ((1 : Matrix (Fin n) (Fin n) ℝ) + (1 / (n : ℝ)) • signMatrix T).det < 5 / 3 :=
  (tournament_skew_kernel_det_le_exp_half T hn).trans_lt exp_half_lt_five_thirds

theorem disjointShortConvolution_le_crude {n : ℕ} (T : Tournament n) (F : Finset (Fin n))
    (K : ℕ) (hn : 0 < n) (hK : 2 * K ≤ n) (hN : 0 < Fᶜ.card) (E : ℝ)
    (hper : ∀ U : Finset (Fin n), U.card < K → Disjoint U F →
      ((adjacency T).submatrix (Subtype.val : (Uᶜ : Finset (Fin n)) → Fin n) Subtype.val).permanent ≤
        (2 * Real.exp (-1) * (1 / 4 : ℝ) ^ F.card * Real.exp E) *
          (((n - U.card).factorial : ℝ) / (2 : ℝ) ^ (n - U.card))) :
    disjointShortConvolution T F K / meanPaths n ≤
      (10 / 3) * (1 / 4 : ℝ) ^ F.card * Real.exp (E + 2 * (K : ℝ) ^ 2 / n) := by
  have h := disjointShortConvolution_le_core_det T F K hn hK
    (2 * Real.exp (-1) * (1 / 4 : ℝ) ^ F.card * Real.exp E) (by positivity) hper
  have hd := (tournament_skew_kernel_det_lt_five_thirds (inducedTournament T Fᶜ) hN).le
  have hm := mul_le_mul_of_nonneg_left hd (by positivity :
    0 ≤ (2 * Real.exp (-1) * (1 / 4 : ℝ) ^ F.card * Real.exp E) * Real.exp 1 *
      Real.exp (2 * (K : ℝ) ^ 2 / n))
  apply h.trans
  convert hm using 1
  rw [Real.exp_add, Real.exp_neg]
  field_simp
  ring


end TournamentHamiltonian

set_option pp.fullNames true
#check TournamentHamiltonian.disjointShortConvolution_le_generating
#print axioms TournamentHamiltonian.disjointShortConvolution_le_generating
#check TournamentHamiltonian.disjointShortConvolution_le_core_det
#print axioms TournamentHamiltonian.disjointShortConvolution_le_core_det
#check TournamentHamiltonian.exp_half_lt_five_thirds
#print axioms TournamentHamiltonian.exp_half_lt_five_thirds
#check TournamentHamiltonian.tournament_skew_kernel_det_lt_five_thirds
#print axioms TournamentHamiltonian.tournament_skew_kernel_det_lt_five_thirds
#check TournamentHamiltonian.disjointShortConvolution_le_crude
#print axioms TournamentHamiltonian.disjointShortConvolution_le_crude
