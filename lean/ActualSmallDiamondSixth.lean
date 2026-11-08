import TournamentOrdinalReconstruction
import OrdinalGlobalSixthDeficit
import SmallDiamondPivotReduction
noncomputable section
namespace ActualSmallDiamondSixth
open Finset DiamondGap PivotCycleLink TriangleCountBridge TournamentOrdinalReconstruction

/-- The sixth-moment deficit for a genuine tournament with small positive
actual diamond count. No SCC decomposition or size/triangle estimate is assumed. -/
theorem actual_small {n : ℕ} (T : DiamondGap.Tournament (Fin n))
    (hn : 4 ≤ n) (hD : 0 < T.diamonds.card) (hsmall : 24*T.diamonds.card ≤ n^2) :
    6*(n : ℝ)^2*(T.diamonds.card : ℝ) ≤
      TwoBlockSixthMoment.third (TransitiveOrbit.T n) -
      TwoBlockSixthMoment.third (IntegerCycleSumBridge.matrix T) := by
  obtain ⟨p,hs,hpos,havg,hhalf,hmoment⟩ :=
    SmallDiamondPivotReduction.exists_pivot T hn hD hsmall
  let U := sourceSwitch T p
  let B := toReal U
  have hnsize : (∑ i ∈ range (count B), (blockSize B i : ℝ)) = (n : ℝ) := by
    exact_mod_cast sum_sizes B
  have hms : ∀ i ∈ range (count B), (blockSize B i : ℝ) ≤
      (TournamentSourceEnergy.cycleCount B : ℝ) := by
    intro i hi
    exact_mod_cast blockSize_le_global B i (mem_range.mp hi) hpos
  have hts : (∑ i ∈ range (count B), OrdinalTournamentDeficit.triangles (block B i)) =
      ((DiamondTriangleIncidence.cyclicTriangles U).card : ℝ) := by
    simp only [OrdinalTournamentDeficit.triangles, ← sum_div]
    rw [cycleCount_sum]
    change (TournamentSourceEnergy.cycleCount (toReal U) : ℝ) / 3 = _
    rw [real_cycleCount_eq_three]
    push_cast
    ring
  have hdi := DiamondTriangleIncidence.diamonds_le_triangles U
  have hdcard : U.diamonds.card = T.diamonds.card :=
    congrArg Finset.card (PivotSmallDiamond.sourceSwitch_diamonds T p)
  rw [Fintype.card_fin, hdcard] at hdi
  have hreal : (T.diamonds.card : ℝ) ≤
      ((n : ℝ)-3)*((DiamondTriangleIncidence.cyclicTriangles U).card : ℝ) := by
    have hh : T.diamonds.card ≤ (n-3)*(DiamondTriangleIncidence.cyclicTriangles U).card := hdi
    have hc : (T.diamonds.card : ℝ) ≤ ((n-3 : ℕ) : ℝ)*
        ((DiamondTriangleIncidence.cyclicTriangles U).card : ℝ) := by exact_mod_cast hh
    simpa only [Nat.cast_sub (show 3 ≤ n by omega), Nat.cast_ofNat] using hc
  have hf := OrdinalGlobalSixthDeficit.conditional_small (blockSize B) (block B)
    (count B) (n : ℝ) (TournamentSourceEnergy.cycleCount B : ℝ)
    (T.diamonds.card : ℝ) hnsize (by exact_mod_cast hn) (by positivity)
    (by exact_mod_cast hhalf) hms (by rw [hts]; exact hreal)
  rw [sum_sizes B] at hf
  change 6*(n : ℝ)^2*(T.diamonds.card : ℝ) ≤
    TwoBlockSixthMoment.third (TransitiveOrbit.T n) -
    TwoBlockSixthMoment.third (OrdinalBlockMatrix.matrix (blockSize B)
      (fun i => (block B i).entry) (count B)) at hf
  rw [sixth_eq B] at hf
  change 6*(n : ℝ)^2*(T.diamonds.card : ℝ) ≤
    TwoBlockSixthMoment.third (TransitiveOrbit.T n) -
      TwoBlockSixthMoment.third (IntegerCycleSumBridge.matrix U) at hf
  rw [hmoment] at hf
  exact hf
end ActualSmallDiamondSixth
#print axioms ActualSmallDiamondSixth.actual_small
