import SmallDiamondPivotReduction
import TournamentComponentBlocks
noncomputable section
namespace SmallDiamondComponentReduction
open Finset DiamondGap PivotCycleLink TriangleCountBridge TournamentComponents TournamentComponentBlocks

def maxComponentSize {n : ℕ} (B : VectorWeakMajorization.Tournament n) : ℕ :=
  (univ : Finset (Component B)).sup (size B)

lemma max_size_le_count {n : ℕ} (B : VectorWeakMajorization.Tournament n)
    (hpos : 0 < TournamentSourceEnergy.cycleCount B) :
    maxComponentSize B ≤ TournamentSourceEnergy.cycleCount B := by
  apply Finset.sup_le
  intro C hC
  exact component_size_le_cycleCount B C hpos

/-- Actual small-diamond source reduction with every actual SCC controlled.
There is no assumed strong-component size or pivot-link inequality. -/
theorem exists_small_components {n : ℕ} (T : Tournament (Fin n)) (hn : 4 ≤ n)
    (hD : 0 < T.diamonds.card) (hsmall : 24*T.diamonds.card ≤ n^2) :
    ∃ p : Fin n,
      (∀ j, j ≠ p → (sourceSwitch T p).S p j = 1) ∧
      n*maxComponentSize (toReal (sourceSwitch T p)) ≤ 12*T.diamonds.card ∧
      2*maxComponentSize (toReal (sourceSwitch T p)) ≤ n ∧
      (∀ C : Component (toReal (sourceSwitch T p)),
        size (toReal (sourceSwitch T p)) C ≤ maxComponentSize (toReal (sourceSwitch T p))) ∧
      TwoBlockSixthMoment.third (IntegerCycleSumBridge.matrix (sourceSwitch T p)) =
        TwoBlockSixthMoment.third (IntegerCycleSumBridge.matrix T) := by
  obtain ⟨p,hs,hpos,havg,hhalf,hmoment⟩ :=
    SmallDiamondPivotReduction.exists_pivot T hn hD hsmall
  have hmax := max_size_le_count (toReal (sourceSwitch T p)) hpos
  refine ⟨p,hs,le_trans (Nat.mul_le_mul_left n hmax) havg,
    le_trans (Nat.mul_le_mul_left 2 hmax) hhalf,?_,hmoment⟩
  intro C
  exact Finset.le_sup (f := size (toReal (sourceSwitch T p))) (mem_univ C)

/-- The requested h≤12D/n form, where h is the actual maximum SCC cardinality. -/
theorem exists_component_fraction_bound {n : ℕ} (T : Tournament (Fin n)) (hn : 4 ≤ n)
    (hD : 0 < T.diamonds.card) (hsmall : 24*T.diamonds.card ≤ n^2) :
    ∃ p : Fin n,
      (maxComponentSize (toReal (sourceSwitch T p)) : ℝ) ≤
          12*(T.diamonds.card : ℝ)/(n : ℝ) ∧
      2*maxComponentSize (toReal (sourceSwitch T p)) ≤ n := by
  obtain ⟨p,hs,hbound,hhalf,hcover,hmoment⟩ := exists_small_components T hn hD hsmall
  refine ⟨p,?_,hhalf⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0<n by omega)
  apply (le_div_iff₀ hnpos).mpr
  have hr : (n : ℝ)*(maxComponentSize (toReal (sourceSwitch T p)) : ℝ) ≤
      12*(T.diamonds.card : ℝ) := by exact_mod_cast hbound
  nlinarith
end SmallDiamondComponentReduction
#print axioms SmallDiamondComponentReduction.exists_small_components
#print axioms SmallDiamondComponentReduction.exists_component_fraction_bound
