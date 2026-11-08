import SignedReferenceConjugacy
import SignedVectorOrbit
noncomputable section
namespace ZigzagOnes
open Finset Matrix ZigzagReference SignedReferenceConjugacy SignedVectorOrbit

def cut (n : ℕ) : ℕ := n/2+1

def plusStep (n : ℕ) : Fin n → ℝ := fun i => if i.val < cut n then 1 else -1

lemma sigma_position (n i : ℕ) (hi : i < n) :
    sigma i = if position n i < cut n then 1 else -1 := by
  unfold sigma position cut
  split_ifs <;> norm_num <;> omega

lemma pullback_ones (n : ℕ) :
    pullback (perm n) (fun i => sigma i.val) (fun _ => 1) = plusStep n := by
  funext i
  simp only [pullback, mul_one]
  rw [sigma_position n ((perm n).symm i).val ((perm n).symm i).isLt]
  have he : position n ((perm n).symm i).val = i.val :=
    congrArg Fin.val ((perm n).apply_symm_apply i)
  rw [he]
  rfl

lemma Q_transpose_action (n : ℕ) (x : Fin n → ℝ) :
    (Q n).transpose.mulVec x = pullback (perm n) (fun i => sigma i.val) x := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Q]
  rw [sum_eq_single ((perm n).symm i)]
  · simp [pullback]
  · intro j hj hne
    have hp : i ≠ perm n j := by
      intro he
      apply hne
      apply (perm n).injective
      simpa using he.symm
    simp [hp]
  · simp

lemma Q_transpose_ones (n : ℕ) :
    (Q n).transpose.mulVec (fun _ => 1) = plusStep n := by
  rw [Q_transpose_action, pullback_ones]
end ZigzagOnes
#print axioms ZigzagOnes.Q_transpose_ones
