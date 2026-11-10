import TournamentHamiltonian.HighVariance
set_option autoImplicit false

/-! Actual convolution mass of short subsets meeting a designated vertex set. -/
namespace TournamentHamiltonian
open scoped Classical Topology
open Filter

noncomputable def meetingSubsets {n : ℕ} (F : Finset (Fin n)) (k : ℕ) : Finset (Finset (Fin n)) :=
  ((Finset.univ : Finset (Fin n)).powersetCard k).filter (fun U => ¬Disjoint U F)

theorem meetingSubsets_card_le {n : ℕ} (F : Finset (Fin n)) (k : ℕ) (hk : 0 < k) :
    (meetingSubsets F k).card ≤ F.card * (n - 1).choose (k - 1) := by
  have heq : meetingSubsets F k = F.biUnion (fun x =>
      ((Finset.univ : Finset (Fin n)).powersetCard k).filter (fun U => x ∈ U)) := by
    ext U
    simp only [meetingSubsets, Finset.mem_filter, Finset.mem_biUnion, Finset.disjoint_left]
    constructor
    · rintro ⟨hU, hd⟩
      push Not at hd
      obtain ⟨x, hxU, hxF⟩ := hd
      exact ⟨x, hxF, hU, hxU⟩
    · rintro ⟨x, hxF, hU, hxU⟩
      exact ⟨hU, fun hd => hd hxU hxF⟩
  rw [heq]
  apply Finset.card_biUnion_le.trans
  have hc (x : Fin n) : (((Finset.univ : Finset (Fin n)).powersetCard k).filter (fun U => x ∈ U)).card =
      (n - 1).choose (k - 1) := by
    have h := Finset.card_filter_powersetCard_subset ({x} : Finset (Fin n)) Finset.univ k
      (Finset.subset_univ _) (by simpa using Nat.succ_le_of_lt hk)
    simpa only [Finset.singleton_subset_iff, Finset.card_singleton, Finset.card_univ,
      Fintype.card_fin] using h
  simp_rw [hc]
  simp

theorem meetingSubsets_zero {n : ℕ} (F : Finset (Fin n)) : meetingSubsets F 0 = ∅ := by
  simp [meetingSubsets]

theorem choose_predecessor_normalization (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    ((n - 1).choose (k - 1) : ℝ) = (k : ℝ) / n * (n.choose k : ℝ) := by
  have h := Nat.add_one_mul_choose_eq (n - 1) (k - 1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ n), Nat.sub_add_cancel (by omega : 1 ≤ k)] at h
  have hR : (n : ℝ) * ((n - 1).choose (k - 1) : ℝ) = (n.choose k : ℝ) * k := by exact_mod_cast h
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp
  nlinarith

theorem sum_meeting_convolution_card_le {n : ℕ} (T : Tournament n) (F : Finset (Fin n))
    (k : ℕ) (hk : k ≤ n) :
    (∑ U ∈ meetingSubsets F k, convolutionTerm T U) ≤
      ((F.card : ℝ) * k / n) * Real.exp 7 * Real.sqrt ((n : ℝ) + 1) *
        (n.factorial : ℝ) / (2 : ℝ) ^ n * subsetWeight k := by
  by_cases hk0 : k = 0
  · subst k
    simp [meetingSubsets_zero]
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
  have hn : 0 < n := lt_of_lt_of_le hkpos hk
  let a : ℝ := Real.exp 7 * Real.sqrt ((n : ℝ) + 1) *
    ((n - k).factorial : ℝ) / (2 : ℝ) ^ (n - k) * (((k : ℝ) + 1) / 2) ^ ((k : ℝ) / 2)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hlocal (U : Finset (Fin n)) (hU : U ∈ meetingSubsets F k) : convolutionTerm T U ≤ a := by
    have hc := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hU).1).2
    simpa only [a, hc] using convolutionTerm_le_stirling T U
  have hcount : ((meetingSubsets F k).card : ℝ) ≤ (F.card : ℝ) * ((n - 1).choose (k - 1) : ℝ) := by
    exact_mod_cast meetingSubsets_card_le F k hkpos
  calc
    _ ≤ ∑ _U ∈ meetingSubsets F k, a := Finset.sum_le_sum hlocal
    _ = (meetingSubsets F k).card * a := by simp
    _ ≤ ((F.card : ℝ) * ((n - 1).choose (k - 1) : ℝ)) * a := mul_le_mul_of_nonneg_right hcount ha
    _ = _ := by
      rw [choose_predecessor_normalization n k hn hkpos, subsetWeight_eq]
      dsimp [a]
      have h := choose_factorial_normalization n k hk
      linear_combination ((F.card : ℝ) * k / n * Real.exp 7 * Real.sqrt ((n : ℝ) + 1) *
        (((k : ℝ) + 1) / 2) ^ ((k : ℝ) / 2)) * h

noncomputable def meetingShortConvolution {n : ℕ} (T : Tournament n) (F : Finset (Fin n)) (K : ℕ) : ℝ :=
  ∑ U, if U.card < K ∧ ¬Disjoint U F then convolutionTerm T U else 0

theorem meetingShortConvolution_le {n : ℕ} (T : Tournament n) (F : Finset (Fin n)) (K : ℕ)
    (hn : 0 < n) :
    meetingShortConvolution T F K ≤ ((F.card : ℝ) * K / n) * Real.exp 7 *
      Real.sqrt ((n : ℝ) + 1) * (n.factorial : ℝ) / (2 : ℝ) ^ n * subsetWeightMass := by
  rw [meetingShortConvolution, sum_finsets_by_card]
  have hlocal (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :
      (∑ U ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        if U.card < K ∧ ¬Disjoint U F then convolutionTerm T U else 0) ≤
      ((F.card : ℝ) * K / n) * Real.exp 7 * Real.sqrt ((n : ℝ) + 1) *
        (n.factorial : ℝ) / (2 : ℝ) ^ n * subsetWeight k := by
    have hkn : k ≤ n := by have := Finset.mem_range.mp hk; omega
    have hW := subsetWeight_nonneg k
    by_cases hkK : k < K
    · have heq : (∑ U ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
          if U.card < K ∧ ¬Disjoint U F then convolutionTerm T U else 0) =
          ∑ U ∈ meetingSubsets F k, convolutionTerm T U := by
        rw [meetingSubsets, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro U hU
        rw [(Finset.mem_powersetCard.mp hU).2]
        simp only [hkK, true_and]
      rw [heq]
      apply (sum_meeting_convolution_card_le T F k hkn).trans
      have hkk : (k : ℝ) ≤ K := by exact_mod_cast hkK.le
      have h := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hkk (by positivity : 0 ≤ (F.card : ℝ))) (by positivity : 0 ≤ (n : ℝ))
      have hh := mul_le_mul_of_nonneg_right h (by positivity : 0 ≤ Real.exp 7 *
        Real.sqrt ((n : ℝ) + 1) * (n.factorial : ℝ) / (2 : ℝ) ^ n * subsetWeight k)
      simpa only [mul_assoc, mul_div_assoc] using hh
    · have heq : (∑ U ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
          if U.card < K ∧ ¬Disjoint U F then convolutionTerm T U else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro U hU
        rw [(Finset.mem_powersetCard.mp hU).2]
        simp [hkK]
      rw [heq]
      positivity
  apply (Finset.sum_le_sum hlocal).trans
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact subsetWeight_summable.sum_le_tsum _ (fun _ _ => subsetWeight_nonneg _)

theorem meetingShortConvolution_normalized_le {n : ℕ} (T : Tournament n) (F : Finset (Fin n))
    (K : ℕ) (hn : 0 < n) :
    meetingShortConvolution T F K / meanPaths n ≤
      ((F.card : ℝ) * K / n) * (Real.exp 7 / 2) * Real.sqrt ((n : ℝ) + 1) * subsetWeightMass := by
  have hp := meetingShortConvolution_le T F K hn
  have hm : 0 < meanPaths n := by unfold meanPaths; positivity
  apply (div_le_iff₀ hm).mpr
  rw [meanPaths_eq_twice_normalization n (by omega)]
  convert hp using 1
  ring

noncomputable def disjointShortConvolution {n : ℕ} (T : Tournament n) (F : Finset (Fin n)) (K : ℕ) : ℝ :=
  ∑ U, if U.card < K ∧ Disjoint U F then convolutionTerm T U else 0

theorem disjoint_add_meeting_short {n : ℕ} (T : Tournament n) (F : Finset (Fin n)) (K : ℕ) :
    disjointShortConvolution T F K + meetingShortConvolution T F K = shortConvolution T K := by
  rw [disjointShortConvolution, meetingShortConvolution, shortConvolution, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro U _
  by_cases hk : U.card < K <;> by_cases hd : Disjoint U F <;> simp [hk, hd]

theorem pathCount_eq_disjoint_meeting_long {n : ℕ} (T : Tournament n) (F : Finset (Fin n)) (K : ℕ) :
    (pathCount T : ℝ) = disjointShortConvolution T F K + meetingShortConvolution T F K + longConvolution T K := by
  rw [disjoint_add_meeting_short, shortConvolution_add_longConvolution]

end TournamentHamiltonian

set_option pp.fullNames true
#check TournamentHamiltonian.meetingSubsets
#print axioms TournamentHamiltonian.meetingSubsets
#check TournamentHamiltonian.meetingSubsets_card_le
#print axioms TournamentHamiltonian.meetingSubsets_card_le
#check TournamentHamiltonian.meetingSubsets_zero
#print axioms TournamentHamiltonian.meetingSubsets_zero
#check TournamentHamiltonian.choose_predecessor_normalization
#print axioms TournamentHamiltonian.choose_predecessor_normalization
#check TournamentHamiltonian.sum_meeting_convolution_card_le
#print axioms TournamentHamiltonian.sum_meeting_convolution_card_le
#check TournamentHamiltonian.meetingShortConvolution
#print axioms TournamentHamiltonian.meetingShortConvolution
#check TournamentHamiltonian.meetingShortConvolution_le
#print axioms TournamentHamiltonian.meetingShortConvolution_le
#check TournamentHamiltonian.meetingShortConvolution_normalized_le
#print axioms TournamentHamiltonian.meetingShortConvolution_normalized_le
#check TournamentHamiltonian.disjointShortConvolution
#print axioms TournamentHamiltonian.disjointShortConvolution
#check TournamentHamiltonian.disjoint_add_meeting_short
#print axioms TournamentHamiltonian.disjoint_add_meeting_short
#check TournamentHamiltonian.pathCount_eq_disjoint_meeting_long
#print axioms TournamentHamiltonian.pathCount_eq_disjoint_meeting_long
