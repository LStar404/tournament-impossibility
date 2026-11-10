import TournamentHamiltonian.SkewSpectrum
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Absolute real determinant bounds for the actual skew tournament kernel. -/
namespace TournamentHamiltonian

private theorem prod_one_add_le_exp_sum (xs : List ℝ) (hxs : ∀ x ∈ xs, 0 ≤ x) :
    (xs.map (fun x => 1 + x)).prod ≤ Real.exp xs.sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha := hxs a (by simp)
    have ht : ∀ x ∈ xs, 0 ≤ x := fun x hx => hxs x (by simp [hx])
    have hp : 0 ≤ (xs.map (fun x => 1 + x)).prod := by
      apply List.prod_nonneg
      intro y hy
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
      linarith [ht x hx]
    have he : 1 + a ≤ Real.exp a := by simpa only [add_comm] using Real.add_one_le_exp a
    simp only [List.map_cons, List.prod_cons, List.sum_cons, Real.exp_add]
    exact mul_le_mul he (ih ht) hp (Real.exp_nonneg a)

theorem tournament_skew_kernel_det_le_exp_half {n : ℕ} (T : Tournament n) (hn : 0 < n) :
    ((1 : Matrix (Fin n) (Fin n) ℝ) + (1 / (n : ℝ)) • signMatrix T).det ≤ Real.exp (1 / 2) := by
  have hdet := signMatrix_normalized_kernel_det T 1
  simp only [one_pow, one_mul] at hdet
  rw [hdet]
  exact (prod_one_add_le_exp_sum (pairedMasses T) (pairedMasses_nonneg T)).trans
    (Real.exp_le_exp.mpr (pairedMasses_sum_lt_half T hn).le)


end TournamentHamiltonian

namespace TournamentHamiltonian
#check prod_one_add_le_exp_sum
#print axioms prod_one_add_le_exp_sum
end TournamentHamiltonian
