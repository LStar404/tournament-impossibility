import ActualSharpPathEnergyCandidate
import QRegularApplications
import PathCountGrowth

/-! Isolated actual sequence/graph asymptotic bridge. No R, F/J, structural
classification, or transcendence-independence hypothesis is assumed for the
actual limit. Downstream nonalgebraicity still retains its explicit LW input. -/
set_option autoImplicit false
noncomputable section
open Filter Topology
namespace ActualExtremalAsymptoticCandidate
open TournamentHamiltonian NonAlgebraicity

/-- Every redundant orientation encoding gives an actual tournament. -/
def orientationTournament {n : ℕ} (o : NonAlgebraicity.Orientation n) :
    TournamentHamiltonian.Tournament n :=
  ⟨NonAlgebraicity.edge o, ⟨NonAlgebraicity.edge_irrefl o,
    fun _i _j hij => NonAlgebraicity.edge_opposite o hij⟩⟩

theorem orientation_pathCount_eq {n : ℕ} (o : NonAlgebraicity.Orientation n) :
    TournamentHamiltonian.pathCount (orientationTournament o) =
      NonAlgebraicity.hamiltonianPathCount o := by
  rfl

/-- Exact equality of the two finite maxima, including order zero. -/
theorem maximalPathCount_eq_maxPaths (n : ℕ) :
    NonAlgebraicity.maximalPathCount n = TournamentHamiltonian.maxPaths n := by
  classical
  apply Nat.le_antisymm
  · unfold NonAlgebraicity.maximalPathCount
    apply Finset.sup_le
    intro o _
    rw [← orientation_pathCount_eq]
    exact TournamentHamiltonian.pathCount_le_maxPaths (orientationTournament o)
  · unfold TournamentHamiltonian.maxPaths
    apply Finset.sup_le
    intro T _
    obtain ⟨o, ho⟩ := NonAlgebraicity.represents_every_tournament T.val
      T.property.1 T.property.2
    have he : NonAlgebraicity.edge o = T.val := funext (fun i => funext (ho i))
    have hp : NonAlgebraicity.IsHamiltonianOrder o = TournamentHamiltonian.IsHamiltonian T := by
      funext p
      unfold NonAlgebraicity.IsHamiltonianOrder TournamentHamiltonian.IsHamiltonian
      rw [he]
    have hc : NonAlgebraicity.hamiltonianPathCount o = TournamentHamiltonian.pathCount T := by
      simp only [NonAlgebraicity.hamiltonianPathCount, TournamentHamiltonian.pathCount, hp]
    rw [← hc]
    exact NonAlgebraicity.pathCount_le_maximal o

theorem normalizedCoefficient_real_eq {n : ℕ} (hn : n ≠ 0) :
    (NonAlgebraicity.normalizedCoefficient n : ℝ) =
      (TournamentHamiltonian.maxPaths n : ℝ) / TournamentHamiltonian.meanPaths n := by
  simp only [NonAlgebraicity.normalizedCoefficient, ite_eq_right hn, Rat.cast_div,
    Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_natCast,
    maximalPathCount_eq_maxPaths, TournamentHamiltonian.meanPaths]
  have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp [hf]

theorem lowerConstant_complex_eq :
    (TournamentHamiltonian.lowerConstant : ℂ) = NonAlgebraicity.extremalConstant := by
  simp [TournamentHamiltonian.lowerConstant, NonAlgebraicity.extremalConstant,
    Complex.ofReal_div, Complex.ofReal_cosh, Complex.ofReal_cos]

theorem actual_maxPaths_normalized_tendsto :
    Tendsto (fun n : ℕ => (TournamentHamiltonian.maxPaths n : ℝ) /
      TournamentHamiltonian.meanPaths n) atTop (𝓝 TournamentHamiltonian.lowerConstant) := by
  obtain ⟨C, hC, N, hN, hb⟩ :=
    ActualSharpPathEnergyCandidate.actual_maxPaths_abs_error_uniform
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hc : Tendsto (fun n : ℕ => C / (n : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    simpa [div_eq_mul_inv] using hi.const_mul C
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [eventually_ge_atTop N, hc.eventually_lt_const hε] with n hn he
  simpa only [Real.dist_eq] using lt_of_le_of_lt (hb n hn) he

/-- Discharges the previously external graph-theoretic asymptotic input. -/
theorem actual_ExtremalAsymptotic : NonAlgebraicity.ExtremalAsymptotic := by
  have hc := (Complex.continuous_ofReal.tendsto TournamentHamiltonian.lowerConstant).comp
    actual_maxPaths_normalized_tendsto
  rw [lowerConstant_complex_eq] at hc
  apply hc.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have h := normalizedCoefficient_real_eq (Nat.ne_of_gt hn)
  have hh := congrArg (fun x : ℝ => (x : ℂ)) h
  simpa only [Complex.ofReal_ratCast, Function.comp_apply] using hh.symm

/-- No R or graph-asymptotic premise remains; the LW input is still explicit. -/
theorem actual_generating_function_nonalgebraic
    (lw : NonAlgebraicity.FourExponentialIndependence) :
    ¬ NonAlgebraicity.HasPolynomialRelation
      (PowerSeries.map (algebraMap ℚ ℂ) NonAlgebraicity.extremalFormalSeries) :=
  NonAlgebraicity.extremal_generating_function_nonalgebraic actual_ExtremalAsymptotic lw

theorem actual_normalizedCoefficient_not_qRegular (q : ℕ) (hq : 2 ≤ q)
    (lw : NonAlgebraicity.FourExponentialIndependence) :
    ¬ NonAlgebraicity.IsQRegular q (fun n => (NonAlgebraicity.normalizedCoefficient n : ℂ)) :=
  NonAlgebraicity.normalizedCoefficient_not_qRegular q hq actual_ExtremalAsymptotic lw

/-- An unconditional growth obstruction for the actual extremal sequence. -/
theorem actual_maximalPathCount_not_exponentially_bounded :
    ¬ ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      ∀ n : ℕ, (NonAlgebraicity.maximalPathCount n : ℝ) ≤ C * D ^ n :=
  NonAlgebraicity.maximalPathCount_not_exponentially_bounded actual_ExtremalAsymptotic

end ActualExtremalAsymptoticCandidate
