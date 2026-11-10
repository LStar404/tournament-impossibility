import TournamentHamiltonian.HighVariance
import ActualTournamentPrescalingBounds

/-! Finite deletion energy and actual competitive-tournament reduction. -/
set_option autoImplicit false
noncomputable section
namespace GlobalEntryFiniteCandidate
open TournamentHamiltonian ActualTournamentPrescalingBounds TournamentPrescalingMassBound
open Filter
open scoped Classical Topology

theorem degreeVariance_induced_le {n : ℕ} (T : Tournament n)
    (U : Finset (Fin n)) :
    degreeVariance (inducedTournament T U) ≤ 2 * degreeVariance T +
      (n : ℝ) * (Uᶜ.card : ℝ) ^ 2 / 2 := by
  have hlocal (i : Fin n) : subsetScore T U i ^ 2 ≤
      2 * score T i ^ 2 + 2 * (Uᶜ.card : ℝ) ^ 2 := by
    have hd := subsetScore_sub_score_abs_le T U i
    have hs := (sq_le_sq₀ (abs_nonneg (subsetScore T U i - score T i))
      (Nat.cast_nonneg Uᶜ.card)).mpr hd
    simp only [sq_abs] at hs
    nlinarith [sq_nonneg (score T i - (subsetScore T U i - score T i))]
  have hs := Finset.sum_le_sum (s := U) (fun i _ => hlocal i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    nsmul_eq_mul] at hs
  have hfull : (∑ i ∈ U, score T i ^ 2) ≤ ∑ i, score T i ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ U) (fun _ _ _ => sq_nonneg _)
  have hcard : (U.card : ℝ) ≤ n := by exact_mod_cast (show U.card ≤ n by simpa using U.card_le_univ)
  have hmul := mul_le_mul_of_nonneg_right hcard (sq_nonneg (Uᶜ.card : ℝ))
  rw [degreeVariance_inducedTournament_eq, degreeVariance_eq_score_sum]
  nlinarith


lemma tau_eq_degreeVariance {n : ℕ} (T : Tournament n) :
    tau (normalizedScore T) = 4 * degreeVariance T / ((n : ℝ) - 1)^2 := by
  rw [degreeVariance_eq_score_sum]
  simp only [tau, normalizedScore, div_pow, ← Finset.sum_div]
  ring

lemma lowVariance_tau_le_log {n : ℕ} (T : Tournament n) (hn : 2 ≤ n)
    (hV : degreeVariance T ≤ 16 * (n : ℝ)^2 * Real.log n) :
    tau (normalizedScore T) ≤ 256 * Real.log (n : ℝ) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
  have hratio : (n : ℝ)^2 ≤ 4 * ((n : ℝ)-1)^2 := by nlinarith
  rw [tau_eq_degreeVariance]
  apply (div_le_iff₀ (sq_pos_of_pos (by linarith : (0 : ℝ) < (n : ℝ)-1))).mpr
  nlinarith [mul_le_mul_of_nonneg_right hratio hlog]

/-- A tournament competing with the averaging benchmark must lie in the
logarithmic variance regime. This assumes only the actual count comparison,
not the desired upper asymptotic or any permanent estimate. -/
theorem competitive_eventually_lowVariance :
    ∀ᶠ n : ℕ in atTop, ∀ T : Tournament n,
      meanPaths n ≤ (pathCount T : ℝ) →
      degreeVariance T < 16 * (n : ℝ)^2 * Real.log n ∧
      tau (normalizedScore T) ≤ 256 * Real.log (n : ℝ) := by
  filter_upwards [highVariance_pathCount_eventually_small
    (ε := 1/2) (by norm_num), eventually_ge_atTop (2 : ℕ)] with n hhigh hn T hcount
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hm : 0 < meanPaths n := by unfold meanPaths; positivity
  have hl : 1 ≤ (pathCount T : ℝ) / meanPaths n :=
    (le_div_iff₀ hm).mpr (by simpa using hcount)
  have hV : degreeVariance T < 16 * (n : ℝ)^2 * Real.log n := by
    by_contra h
    have hh := hhigh T (le_of_not_gt h)
    have hs : (1/2 : ℝ) / n < 1 := (div_lt_iff₀ hn0).mpr (by linarith)
    linarith
  exact ⟨hV, lowVariance_tau_le_log T hn hV.le⟩

end GlobalEntryFiniteCandidate
set_option pp.fullNames true
#check GlobalEntryFiniteCandidate.degreeVariance_induced_le
#print axioms GlobalEntryFiniteCandidate.degreeVariance_induced_le
#check GlobalEntryFiniteCandidate.tau_eq_degreeVariance
#print axioms GlobalEntryFiniteCandidate.tau_eq_degreeVariance
#check GlobalEntryFiniteCandidate.lowVariance_tau_le_log
#print axioms GlobalEntryFiniteCandidate.lowVariance_tau_le_log
#check GlobalEntryFiniteCandidate.competitive_eventually_lowVariance
#print axioms GlobalEntryFiniteCandidate.competitive_eventually_lowVariance
