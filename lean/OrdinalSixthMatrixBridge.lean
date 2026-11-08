import OrdinalBlockMatrix
import TwoBlockSixthMoment
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OrdinalSixthMatrixBridge
open Finset Matrix OrdinalBlockMatrix OrdinalMomentRecurrence

lemma packet_sixth (m : ℕ → ℕ)
    (A : ∀ i, Matrix (Fin (m i)) (Fin (m i)) ℝ) (i : ℕ) :
    (packet m A i).sixth = TwoBlockSixthMoment.third (A i) := by
  simp only [packet, TwoBlockSixthMoment.third, RectangularFrobenius.sqnorm,
    RectangularFrobenius.inner, pow_two]

/-- Actual Frobenius sixth moment of every finite ordered block matrix.
No determinant-coefficient or moment-recurrence hypothesis is assumed. -/
theorem sixth_eq_cumulative (m : ℕ → ℕ)
    (A : ∀ i, Matrix (Fin (m i)) (Fin (m i)) ℝ)
    (hA : ∀ k i j, A k i j = -A k j i) (k : ℕ) :
    TwoBlockSixthMoment.third (matrix m A k) = (cumulative (packet m A) k).sixth := by
  induction k with
  | zero =>
    unfold TwoBlockSixthMoment.third RectangularFrobenius.sqnorm RectangularFrobenius.inner
    change (∑ i : Fin 0, _) = 0
    exact Finset.sum_eq_zero (fun i _ => Fin.elim0 i)
  | succ k ih =>
    change TwoBlockSixthMoment.third (TwoBlockEnergy.join (matrix m A k) (A k)) = _
    rw [TwoBlockSixthMoment.third_join _ _ (skew m A hA k) (hA k), ih,
      (source_energies m A hA k).1, (source_energies m A hA k).2]
    simp only [cumulative, join, packet_cumulative_size, Fintype.card_fin,
      packet, TwoBlockSixthMoment.third, RectangularFrobenius.sqnorm,
      RectangularFrobenius.inner, pow_two]

/-- The finite coefficient polynomial (★) is now identified with the actual
sixth Frobenius moment, through real block-matrix recurrences, not formal log. -/
theorem actual_sixth_coefficient (m : ℕ → ℕ)
    (A : ∀ i, Matrix (Fin (m i)) (Fin (m i)) ℝ)
    (hA : ∀ k i j, A k i j = -A k j i) (k : ℕ) :
    TwoBlockSixthMoment.third (matrix m A k) =
      6*OrdinalSixthPolynomial.coefficient (range k) (∑ i ∈ range k, (m i : ℝ))
        (fun i => (m i : ℝ)) (fun i => TwoBlockEnergy.first (A i))
        (fun i => TwoBlockEnergy.second (A i)) (fun i => TwoBlockSixthMoment.third (A i)) := by
  rw [sixth_eq_cumulative m A hA k, cumulative_sixth]
  simp only [packet, TwoBlockSixthMoment.third, RectangularFrobenius.sqnorm,
    RectangularFrobenius.inner, pow_two]
end OrdinalSixthMatrixBridge
#print axioms OrdinalSixthMatrixBridge.actual_sixth_coefficient
