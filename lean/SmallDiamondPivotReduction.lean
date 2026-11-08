import PivotSmallDiamond
import PivotMomentInvariant
import TriangleCountBridge
noncomputable section
namespace SmallDiamondPivotReduction
open DiamondGap DiamondFreeRepresentation PivotCycleLink TriangleCountBridge

/-- An unconditional finite reduction for actual small positive diamond count.
The output directed-cycle count is the genuine finite set cardinality and the
actual sixth moment is preserved by the produced source switch. -/
theorem exists_pivot {n : ℕ} (T : Tournament (Fin n)) (hn : 4 ≤ n)
    (hD : 0 < T.diamonds.card) (hsmall : 24*T.diamonds.card ≤ n^2) :
    ∃ p : Fin n,
      (∀ j, j ≠ p → (sourceSwitch T p).S p j = 1) ∧
      0 < TournamentSourceEnergy.cycleCount (toReal (sourceSwitch T p)) ∧
      n*TournamentSourceEnergy.cycleCount (toReal (sourceSwitch T p)) ≤ 12*T.diamonds.card ∧
      2*TournamentSourceEnergy.cycleCount (toReal (sourceSwitch T p)) ≤ n ∧
      TwoBlockSixthMoment.third (IntegerCycleSumBridge.matrix (sourceSwitch T p)) =
        TwoBlockSixthMoment.third (IntegerCycleSumBridge.matrix T) := by
  obtain ⟨p,hpos,havg,hsize⟩ := PivotSmallDiamond.exists_small_source_cycles T
    (by simpa only [Fintype.card_fin] using hn) hD
    (by simpa only [Fintype.card_fin] using hsmall)
  simp only [Fintype.card_fin] at havg hsize
  refine ⟨p,pivot_source T p,?_,?_,?_,PivotMomentInvariant.sixth_eq T p⟩
  all_goals rw [real_cycleCount_eq_three]
  · omega
  · nlinarith
  · nlinarith
end SmallDiamondPivotReduction
#print axioms SmallDiamondPivotReduction.exists_pivot
