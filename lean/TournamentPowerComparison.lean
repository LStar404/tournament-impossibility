import IteratedVectorMajorization
noncomputable section
namespace TournamentPowerComparison
open Finset VectorWeakMajorization TournamentSwitching IteratedVectorMajorization

def basis {n : ℕ} (j : Fin n) : Fin n → ℝ := Pi.single j 1

lemma basis_permuted {n : ℕ} (j l : Fin n) :
    (fun i => basis j (Equiv.swap j l i)) = basis l := by
  funext i
  by_cases hij : i = j <;> by_cases hil : i = l <;>
    simp_all [basis, Pi.single_apply, Equiv.swap_apply_def]

lemma sorted_basis_eq {n : ℕ} (j l : Fin n) : sortedPad (basis j) = sortedPad (basis l) := by
  have h := sortedPad_perm (basis j) (Equiv.swap j l)
  rw [basis_permuted] at h
  exact h.symm

/-- Explicitly give the entries Matrix multiplication, not pointwise powers. -/
def matrix {n : ℕ} (B : Tournament n) : Matrix (Fin n) (Fin n) ℝ := B.entry

lemma trajectory_eq_mulVec {n : ℕ} (B : Tournament n) (x : Fin n → ℝ) (r : ℕ) :
    trajectory (fun _ => B) x r = (matrix B ^ r).mulVec x := by
  induction r with
  | zero => simp [trajectory]
  | succ r ih =>
    rw [trajectory, ih, pow_succ']
    rw [← Matrix.mulVec_mulVec]
    rfl

lemma trajectory_basis {n : ℕ} (B : Tournament n) (j : Fin n) (r : ℕ) (i : Fin n) :
    trajectory (fun _ => B) (basis j) r i = (matrix B ^ r) i j := by
  rw [trajectory_eq_mulVec]
  simp [basis, Matrix.mulVec_single_one]

/-- Every column has the same proven K-reference upper bound, without yet
identifying the K orbit with a transitive-tournament column. -/
theorem column_power_bound {n : ℕ} (B : Tournament n) (j l : Fin n) (r : ℕ) :
    (∑ i : Fin n, ((matrix B ^ r) i j)^2) ≤
      ∑ i ∈ range n, (comparison n (sortedPad (basis l)) r i)^2 := by
  have h := fixed_trajectory_sum_sq_le B (basis j) r
  simp only [trajectory_basis] at h
  rw [sorted_basis_eq j l] at h
  exact h

/-- All integer powers, with the squared Frobenius norm expanded explicitly.
The right side is K's actual basis orbit, not an assumed T comparison. -/
theorem frobenius_power_bound {n : ℕ} (B : Tournament n) (l : Fin n) (r : ℕ) :
    (∑ j : Fin n, ∑ i : Fin n, ((matrix B ^ r) i j)^2) ≤
      (n : ℝ) * (∑ i ∈ range n, (comparison n (sortedPad (basis l)) r i)^2) := by
  calc
    _ ≤ ∑ _j : Fin n, ∑ i ∈ range n, (comparison n (sortedPad (basis l)) r i)^2 := by
      apply sum_le_sum
      intro j hj
      exact column_power_bound B j l r
    _ = _ := by simp
end TournamentPowerComparison
#print axioms TournamentPowerComparison.trajectory_eq_mulVec
#print axioms TournamentPowerComparison.frobenius_power_bound
