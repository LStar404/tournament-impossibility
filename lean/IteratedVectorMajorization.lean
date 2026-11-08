import SelectedTournamentMajorization
noncomputable section
namespace IteratedVectorMajorization
open Finset VectorWeakMajorization MajorizationCone TournamentSwitching SelectedTournamentMajorization

def trajectory {n : ℕ} (B : ℕ → Tournament n) (x : Fin n → ℝ) : ℕ → Fin n → ℝ
  | 0 => x
  | r+1 => (B r).act (trajectory B x r)

def comparison (n : ℕ) (z : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => z
  | r+1 => K n (comparison n z r)

lemma comparison_endpoint (n : ℕ) (z : ℕ → ℝ) (hz : z n = 0) (r : ℕ) :
    comparison n z r n = 0 := by
  cases r with
  | zero => exact hz
  | succ r => simp [comparison, K]

lemma comparison_cone (n : ℕ) (z : ℕ → ℝ) (hz : DescendingNonnegative n z)
    (hzero : z n = 0) (r : ℕ) : DescendingNonnegative n (comparison n z r) := by
  induction r with
  | zero => exact hz
  | succ r ih =>
    exact K_preserves_cone n (comparison n z r) ih (comparison_endpoint n z hzero r)

/-- No fixed-matrix assumption: the tournament may vary at every step. -/
theorem trajectory_majorized {n : ℕ} (B : ℕ → Tournament n) (x : Fin n → ℝ) (r : ℕ) :
    WeakMajorized n (sortedPad (trajectory B x r)) (comparison n (sortedPad x) r) := by
  induction r with
  | zero => intro k hk; exact le_rfl
  | succ r ih =>
    have hs := tournament_vector_majorization (B r) (trajectory B x r)
    have ht := K_preserves_prefix_order n _ _ ih
    intro k hk
    exact le_trans (hs k hk) (ht k hk)

lemma sortedPad_sum_sq {n : ℕ} (x : Fin n → ℝ) :
    (∑ i ∈ range n, (sortedPad x i)^2) = ∑ i : Fin n, (x i)^2 := by
  rw [← Fin.sum_univ_eq_sum_range]
  have he : (∑ i : Fin n, (sortedPad x i.val)^2) =
      ∑ i : Fin n, (x (absSort x i))^2 := by
    apply sum_congr rfl
    intro i hi
    simp [sortedPad, i.isLt, sq_abs]
  rw [he]
  exact Equiv.sum_comp (absSort x) (fun i => (x i)^2)

/-- Squared Euclidean norm domination by the actual K trajectory. -/
theorem trajectory_sum_sq_le {n : ℕ} (B : ℕ → Tournament n) (x : Fin n → ℝ) (r : ℕ) :
    (∑ i : Fin n, (trajectory B x r i)^2) ≤
      ∑ i ∈ range n, (comparison n (sortedPad x) r i)^2 := by
  have hh := sum_sq_le n _ _ (trajectory_majorized B x r)
    (sortedPad_cone (trajectory B x r))
    (comparison_cone n (sortedPad x) (sortedPad_cone x) (sortedPad_endpoint x) r)
  rw [sortedPad_sum_sq] at hh
  exact hh

/-- Constant tournaments give every integer matrix-power trajectory. -/
theorem fixed_trajectory_sum_sq_le {n : ℕ} (B : Tournament n) (x : Fin n → ℝ) (r : ℕ) :
    (∑ i : Fin n, (trajectory (fun _ => B) x r i)^2) ≤
      ∑ i ∈ range n, (comparison n (sortedPad x) r i)^2 :=
  trajectory_sum_sq_le (fun _ => B) x r
end IteratedVectorMajorization
#print axioms IteratedVectorMajorization.trajectory_majorized
#print axioms IteratedVectorMajorization.trajectory_sum_sq_le
#print axioms IteratedVectorMajorization.fixed_trajectory_sum_sq_le
