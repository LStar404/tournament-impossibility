import PivotCycleLink
import IntegerCycleSumBridge
import SignedConjugacy
import TwoBlockSixthMoment
noncomputable section
namespace PivotMomentInvariant
open Finset Matrix DiamondGap DiamondFreeRepresentation PivotCycleLink

/-- Exact natural-power Frobenius invariance for the actual source switch. -/
theorem power_norm_eq {n : ℕ} (T : Tournament (Fin n)) (p : Fin n) (r : ℕ) :
    (∑ i, ∑ j, (((IntegerCycleSumBridge.matrix (sourceSwitch T p))^r) i j)^2) =
      ∑ i, ∑ j, (((IntegerCycleSumBridge.matrix T)^r) i j)^2 := by
  let s : Fin n → ℝ := fun i => (pivotSign T p i : ℝ)
  have hs : ∀ i, s i*s i=1 := by
    intro i
    have h := pivotSign_sq T p i
    dsimp [s]
    exact_mod_cast (show pivotSign T p i*pivotSign T p i=1 by simpa only [pow_two] using h)
  have hrel : SignedConjugacy.Related (Equiv.refl _) s
      (IntegerCycleSumBridge.matrix (sourceSwitch T p)) (IntegerCycleSumBridge.matrix T) := by
    intro i j
    simp only [IntegerCycleSumBridge.matrix, Matrix.of_apply, sourceSwitch, switched,
      Int.cast_mul, Equiv.refl_apply]
    dsimp [s]
    ring
  have hp := SignedConjugacy.related_pow (Equiv.refl _) s hs _ _ hrel r
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  rw [hp i j]
  simp only [Equiv.refl_apply, mul_pow]
  rw [pow_two (s i), pow_two (s j), hs, hs]
  ring

/-- The source switch preserves the actual sixth Frobenius moment. -/
theorem sixth_eq {n : ℕ} (T : Tournament (Fin n)) (p : Fin n) :
    TwoBlockSixthMoment.third (IntegerCycleSumBridge.matrix (sourceSwitch T p)) =
      TwoBlockSixthMoment.third (IntegerCycleSumBridge.matrix T) := by
  simpa only [TwoBlockSixthMoment.third, RectangularFrobenius.sqnorm,
    RectangularFrobenius.inner, pow_two] using power_norm_eq T p 3
end PivotMomentInvariant
#print axioms PivotMomentInvariant.power_norm_eq
#print axioms PivotMomentInvariant.sixth_eq
