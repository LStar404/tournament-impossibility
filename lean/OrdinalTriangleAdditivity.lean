import OrdinalBlockMatrix
import TournamentSourceEnergy
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OrdinalTriangleAdditivity
open Finset Matrix OrdinalBlockMatrix VectorWeakMajorization TournamentPowerComparison

def cycleSum {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, if A i j = 1 ∧ A j k = 1 ∧ A k i = 1 then 1 else 0

/-- No directed cycle can cross a two-block ordered join. -/
lemma cycleSum_join {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ) :
    cycleSum (TwoBlockEnergy.join A B) = cycleSum A+cycleSum B := by
  unfold cycleSum
  simp only [Fintype.sum_sum_type, TwoBlockEnergy.join,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    sum_add_distrib, show (-1 : ℝ) ≠ 1 by norm_num,
    eq_self_iff_true, false_and, and_false, true_and, and_true,
    ite_false, ite_true, sum_const_zero, add_zero, zero_add]

lemma cycleSum_tournament {n : ℕ} (B : Tournament n) :
    cycleSum (TournamentPowerComparison.matrix B) = (TournamentSourceEnergy.cycleCount B : ℝ) := by
  exact (TournamentSourceEnergy.count_as_sum B).symm

/-- Actual ordered-block triangle totals are the sums of their internal totals;
this is a matrix statement, not a supplied decomposition-count assumption. -/
theorem cycleSum_ordinal (m : ℕ → ℕ)
    (A : ∀ i, Matrix (Fin (m i)) (Fin (m i)) ℝ) (k : ℕ) :
    cycleSum (OrdinalBlockMatrix.matrix m A k) = ∑ i ∈ range k, cycleSum (A i) := by
  induction k with
  | zero =>
    unfold cycleSum
    change (∑ i : Fin 0, _) = _
    simp
  | succ k ih =>
    change cycleSum (TwoBlockEnergy.join (OrdinalBlockMatrix.matrix m A k) (A k)) = _
    rw [cycleSum_join, ih, sum_range_succ]

theorem cycleSum_tournament_ordinal (m : ℕ → ℕ) (B : ∀ i, Tournament (m i)) (k : ℕ) :
    cycleSum (OrdinalBlockMatrix.matrix m (fun i => TournamentPowerComparison.matrix (B i)) k) =
      ∑ i ∈ range k, (TournamentSourceEnergy.cycleCount (B i) : ℝ) := by
  rw [cycleSum_ordinal]
  apply sum_congr rfl
  intro i hi
  exact cycleSum_tournament (B i)
end OrdinalTriangleAdditivity
#print axioms OrdinalTriangleAdditivity.cycleSum_tournament_ordinal
