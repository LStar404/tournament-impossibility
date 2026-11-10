import ExceptionalDisjointCandidate
import ExceptionalMeetingSmall
import LogWindowErrorCandidate
set_option autoImplicit false
noncomputable section
namespace TournamentHamiltonian
open scoped Classical Topology
open Filter

theorem exceptional_pathCount_le_191_of_crude_bound {n : ℕ} (T : Tournament n)
    (F : Finset (Fin n)) (K : ℕ) (hn : 0 < n) (hK : 2 * K ≤ n)
    (hN : 0 < Fᶜ.card) (hF : 1 ≤ F.card) (E : ℝ)
    (hE : Real.exp (E + 2 * (K : ℝ) ^ 2 / n) ≤ 21 / 20)
    (hm : meetingShortConvolution T F K / meanPaths n ≤ 1 / 25)
    (hl : longConvolution T K / meanPaths n ≤ 1 / 25)
    (hper : ∀ U : Finset (Fin n), U.card < K → Disjoint U F →
      ((adjacency T).submatrix (Subtype.val : (Uᶜ : Finset (Fin n)) → Fin n) Subtype.val).permanent ≤
        (2 * Real.exp (-1) * (1 / 4 : ℝ) ^ F.card * Real.exp E) *
          (((n - U.card).factorial : ℝ) / (2 : ℝ) ^ (n - U.card))) :
    (pathCount T : ℝ) / meanPaths n ≤ 191 / 200 := by
  have hp : (1 / 4 : ℝ) ^ F.card ≤ 1 / 4 := by
    simpa only [pow_one] using pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num : (1 / 4 : ℝ) ≤ 1) hF
  have hd := disjointShortConvolution_le_crude T F K hn hK hN E hper
  have hb := mul_le_mul (mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 10 / 3))
    hE (Real.exp_nonneg _) (by norm_num : (0 : ℝ) ≤ (10 / 3) * (1 / 4))
  have hsum : (pathCount T : ℝ) / meanPaths n =
      disjointShortConvolution T F K / meanPaths n + meetingShortConvolution T F K / meanPaths n +
        longConvolution T K / meanPaths n := by
    rw [pathCount_eq_disjoint_meeting_long T F K, add_div, add_div]
  have hbound : (pathCount T : ℝ) / meanPaths n ≤ 191 / 200 := by rw [hsum]; nlinarith
  exact hbound

theorem convolution_cutoff_error_eventually_small (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop, 2 * (subsetCutoff n : ℝ) ^ 2 / n ≤ eps := by
  have hlim := (LogWindowErrorCandidate.log_sqrt_decay 2).const_mul (2 : ℝ)
  simp only [mul_zero] at hlim
  filter_upwards [hlim.eventually_le_const heps, short_cutoff_eventually_small] with n he hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hk2 := (sq_le_sq₀ (by positivity : 0 ≤ (subsetCutoff n : ℝ)) hlog).mpr hn.2.1
  have h1 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hk2 (by norm_num : (0 : ℝ) ≤ 2)) hn0.le
  have hs : Real.sqrt n ≤ n := by nlinarith [Real.sq_sqrt hn0.le, Real.sqrt_nonneg (n : ℝ)]
  have h2 := div_le_div_of_nonneg_left (by positivity : 0 ≤ 2 * Real.log (n : ℝ) ^ 2)
    (Real.sqrt_pos.mpr hn0) hs
  apply h1.trans
  apply h2.trans
  simpa only [mul_div_assoc] using he


/-- Uniform four-block error budget; the threshold is independent of f,N,T,U. -/
theorem exceptional_assembly_error_eventually_small (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop, ∀ f N : ℝ,
      0 ≤ f → f ≤ 400 * Real.log (n : ℝ) → (n : ℝ) / 2 ≤ N →
      292 * f ^ 2 / N ≤ eps := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)^2 / (n : ℝ)) atTop (𝓝 0) := by
    simpa using LogWindowErrorCandidate.log_power_decay 2 (by norm_num : (0 : ℝ) < 1)
  have hlim := hlog.const_mul (93440000 : ℝ)
  simp only [mul_zero] at hlim
  filter_upwards [hlim.eventually_le_const heps, eventually_ge_atTop (1 : ℕ)]
    with n he hn f N hf hfa hN
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : 0 < N := by linarith
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hf2 := (sq_le_sq₀ hf (by positivity : 0 ≤ 400 * Real.log (n : ℝ))).mpr hfa
  have h1 := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hf2 (by norm_num : (0 : ℝ) ≤ 292)) hN0.le
  have h2 := div_le_div_of_nonneg_left
    (by positivity : 0 ≤ 292 * (400 * Real.log (n : ℝ)) ^ 2)
    (by positivity : 0 < (n : ℝ) / 2) hN
  apply h1.trans (h2.trans _)
  have heq : 292 * (400 * Real.log (n : ℝ)) ^ 2 / ((n : ℝ) / 2) =
      93440000 * (Real.log (n : ℝ)^2 / (n : ℝ)) := by field_simp; ring
  rw [heq]
  exact he

end TournamentHamiltonian

set_option pp.fullNames true
#check TournamentHamiltonian.exceptional_pathCount_le_191_of_crude_bound
#print axioms TournamentHamiltonian.exceptional_pathCount_le_191_of_crude_bound
#check TournamentHamiltonian.convolution_cutoff_error_eventually_small
#print axioms TournamentHamiltonian.convolution_cutoff_error_eventually_small
#check TournamentHamiltonian.exceptional_assembly_error_eventually_small
#print axioms TournamentHamiltonian.exceptional_assembly_error_eventually_small
