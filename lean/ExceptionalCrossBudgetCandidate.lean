import ExceptionalCoreGeometryCandidate

/-! Isolated actual exceptional-core weighted cross interface.
No old analytic preconditioning modules or final path estimates are imported. -/
set_option autoImplicit false
noncomputable section
namespace TournamentHamiltonian
open ActualTournamentPrescalingBounds TournamentPrescalingMassBound TournamentPrescalingMass
open scoped Classical Topology
open Filter

noncomputable def exceptionalCrossEps (n : ℕ) : ℝ := 2 * (401 * Real.log (n : ℝ) + 1) / n

noncomputable def exceptionalCrossBeta (n : ℕ) : ℝ := 20 * Real.sqrt (2400 * Real.log (n : ℝ) / n)

noncomputable def exceptionalCrossCap (n : ℕ) : ℝ :=
  19 / 100 + 4 * exceptionalCrossEps n + 4 * exceptionalCrossBeta n + 4 * exceptionalCrossBeta n ^ 2

theorem exceptionalCrossBeta_tendsto_zero : Tendsto exceptionalCrossBeta atTop (𝓝 0) := by
  have hlog := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have h := (hlog.const_mul 2400).sqrt.const_mul 20
  simp only [mul_zero, Real.sqrt_zero] at h
  convert h using 1
  ext n
  dsimp [exceptionalCrossBeta]
  congr 2
  ring

theorem exceptionalCrossCap_tendsto : Tendsto exceptionalCrossCap atTop (𝓝 (19 / 100)) := by
  have hlog := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hinv := tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have heps := ((hlog.const_mul 802).add (hinv.const_mul 2))
  have hb := exceptionalCrossBeta_tendsto_zero
  have h := ((((tendsto_const_nhds : Tendsto (fun _ : ℕ => (19 / 100 : ℝ)) atTop (𝓝 (19 / 100 : ℝ))).add (heps.const_mul 4)).add (hb.const_mul 4)).add ((hb.pow 2).const_mul 4))
  simp only [mul_zero, add_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at h
  convert h using 1
  ext n
  dsimp [exceptionalCrossCap, exceptionalCrossEps]
  ring

theorem exceptional_cross_profiles_uniform_eventually :
    ∀ᶠ n : ℕ in atTop, ∀ d N beta : ℝ,
      0 ≤ d → d ≤ 401 * Real.log (n : ℝ) → (n : ℝ) / 2 ≤ N →
      0 ≤ beta → beta ≤ exceptionalCrossBeta n →
      19 / 100 + 4 * ((d + 1) / N) + 4 * beta + 4 * beta ^ 2 ≤ 1 / 4 ∧
        2 + 2 * beta ≤ 3 := by
  filter_upwards [exceptionalCrossCap_tendsto.eventually_le_const (by norm_num : (19 / 100 : ℝ) < 1 / 4),
    exceptionalCrossBeta_tendsto_zero.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2),
    eventually_ge_atTop (1 : ℕ)] with n hc hb hn d N beta hd hdA hN hbeta hbetaA
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hN0 : 0 < N := by linarith
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hb0 : 0 ≤ exceptionalCrossBeta n := by unfold exceptionalCrossBeta; positivity
  have heps : (d + 1) / N ≤ exceptionalCrossEps n := by
    apply (div_le_div_of_nonneg_right (add_le_add hdA (le_refl 1)) hN0.le).trans
    dsimp [exceptionalCrossEps]
    have h := div_le_div_of_nonneg_left (by positivity : 0 ≤ 401 * Real.log (n : ℝ) + 1)
      (by positivity : 0 < (n : ℝ) / 2) hN
    convert h using 1; ring
  have hs := (sq_le_sq₀ hbeta hb0).mpr hbetaA
  constructor
  · apply le_trans _ hc
    dsimp [exceptionalCrossCap]
    linarith
  · linarith

end TournamentHamiltonian
