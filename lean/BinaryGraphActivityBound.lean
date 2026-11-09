import QuantitativeFixedActivity
import BinaryRawGraphWeighted
noncomputable section
namespace BinaryGraphActivityBound
open BinaryBalancedTensor WeightedCoefficientNorm

def rawActivity {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (j : ℕ) : PowerSeries ℂ :=
  ActualFiniteActivity.series (FullWickSquarefreeCompatibility.block M)
    RawFormalMixedSpecialization.identityInteraction (FullWickSquarefreeCompatibility.block_symm M)
    ActualResidualFrozenFactorization.identity_symmetry (fun _ => 1) j

theorem block_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    FullWickSquarefreeCompatibility.block M=BipartiteOperatorBound.block M M.transpose := by
  funext x y
  cases x <;> cases y <;> rfl

def coordinateConstant (r : ℕ) : ℝ := (1025/2)*((2:ℝ)^(r+1)+1)

theorem bound {C : Type*} [Fintype C] [DecidableEq C] {n : ℕ}
    (hn : 24 ≤ n) (r : ℕ) (e : Bits (r+1) ≃ Fin (2^(r+1))) (B : Matrix C C ℝ)
    (hB : ∀i j,B j i= -B i j) (he : ∀i j,|B i j| ≤ 1)
    (f : Fin n ≃ C × Bits (r+1)) (v : ℝ) (hv : |v| ≤ 1) (j : ℕ) (hj : 1 ≤ j) :
    let M := TournamentSkewMargin.branch (BinaryRawGraphWeighted.realGraph (r+1) e B f) v
    Finite (9/8) (rawActivity M j) ∧ norm (9/8) (rawActivity M j) ≤
      (QuantitativeFixedActivity.totalConstant (coordinateConstant r)*(j:ℝ)/(n:ℝ))^j := by
  dsimp only
  have hw := BinaryRawGraphWeighted.weighted hn r e B hB he f v hv
  dsimp only at hw
  rw [← block_eq] at hw
  have hp : (1:ℝ) ≤ coordinateConstant r := by
    dsimp [coordinateConstant]
    have hh : 0 ≤ (2:ℝ)^(r+1) := by positivity
    linarith
  have hm : (1025/2:ℝ) ≤ coordinateConstant r := by
    dsimp [coordinateConstant]
    have hh : 0 ≤ (2:ℝ)^(r+1) := by positivity
    linarith
  apply QuantitativeFixedActivity.bound (n:=n) (by omega) (by simp; omega) _ _ _ _ _ j hj
    (9/8) (coordinateConstant r) (by norm_num) hp
    (fun i j => (hw.1 i j).1) (fun i => (hw.2 i).1)
  · intro i j
    exact (hw.1 i j).2.trans (div_le_div_of_nonneg_right hm (Nat.cast_nonneg n))
  · intro i
    exact (hw.2 i).2
end BinaryGraphActivityBound
#print axioms BinaryGraphActivityBound.bound
