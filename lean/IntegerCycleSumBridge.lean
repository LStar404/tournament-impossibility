import OrdinalTriangleAdditivity
import TriangleCountBridge

/-! Integer tournament counts and real matrix cycle sums on the identical
finite carrier. No Fin relabeling or unproved count conversion is used. -/
namespace IntegerCycleSumBridge
open Finset DiamondGap DiamondTriangleIncidence TriangleCountBridge
variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Entrywise casting keeps the underlying finite vertex type unchanged. -/
noncomputable def matrix (T : Tournament V) : Matrix V V ℝ := Matrix.of fun i j => (T.S i j : ℝ)

lemma directed_card_as_sum (T : Tournament V) :
    ((directedTriples T).card : ℝ) =
      ∑ i, ∑ j, ∑ k, if T.S i j=1 ∧ T.S j k=1 ∧ T.S k i=1 then (1:ℝ) else 0 := by
  unfold directedTriples
  rw [← Finset.sum_boole]
  simp only [Fintype.sum_prod_type]

/-- Exact equality of the existing real cycleSum with the actual ordered set cardinality. -/
theorem cycleSum_eq_ordered (T : Tournament V) :
    OrdinalTriangleAdditivity.cycleSum (matrix T) = ((directedTriples T).card : ℝ) := by
  rw [directed_card_as_sum]
  simp only [OrdinalTriangleAdditivity.cycleSum, matrix, Matrix.of_apply, Int.cast_eq_one]

/-- The generic real matrix cycle sum is three times the actual unordered count. -/
theorem cycleSum_eq_three_unordered (T : Tournament V) :
    OrdinalTriangleAdditivity.cycleSum (matrix T) = 3*((cyclicTriangles T).card : ℝ) := by
  rw [cycleSum_eq_ordered, ordered_eq_three_unordered]
  simp only [Nat.cast_mul, Nat.cast_ofNat]

/-- Exposed Matrix.of endpoint for callers with a pre-existing block carrier. -/
theorem cycleSum_of_eq_three_unordered (T : Tournament V) :
    OrdinalTriangleAdditivity.cycleSum (Matrix.of fun i j => (T.S i j : ℝ)) =
      3*((cyclicTriangles T).card : ℝ) :=
  cycleSum_eq_three_unordered T

/-- Genuine diamond-count bound expressed directly in the generic matrix cycle sum. -/
theorem three_diamonds_le_cycleSum (T : Tournament V) :
    3*(T.diamonds.card : ℝ) ≤ ((Fintype.card V-3 : ℕ) : ℝ)*
      OrdinalTriangleAdditivity.cycleSum (matrix T) := by
  rw [cycleSum_eq_ordered]
  exact_mod_cast three_diamonds_le_ordered T

end IntegerCycleSumBridge
#print axioms IntegerCycleSumBridge.cycleSum_eq_ordered
#print axioms IntegerCycleSumBridge.cycleSum_of_eq_three_unordered
#print axioms IntegerCycleSumBridge.three_diamonds_le_cycleSum
