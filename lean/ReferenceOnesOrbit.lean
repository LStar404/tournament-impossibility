import ZigzagOnes
import SignedCycleOnes
import ReferenceMomentComparison
noncomputable section
namespace ReferenceOnesOrbit
open Finset Matrix ReferenceDiagonal ZigzagReference ZigzagOnes SignedVectorOrbit
open ReferenceMomentComparison

lemma reference_vector_norm (n r : ℕ) (x : Fin n → ℝ) :
    (∑ i, ((Kmatrix n ^ r).mulVec x i)^2) =
      ∑ i, ((Tmatrix n ^ r).mulVec (pullback (perm n) (fun j => sigma j.val) x) i)^2 := by
  apply norm_sq_transport (Kmatrix n) (Tmatrix n) (K_normal n) (T_normal n)
    (perm n) (fun j => sigma j.val) (fun j => sigma_sq j.val)
  intro i j
  rw [Kmatrix_symmetric, T_transpose]
  simpa only [pow_two, neg_mul] using SignedReferenceConjugacy.concrete_entry n i j

lemma cut_le (d : ℕ) : cut (d+1) ≤ d+1 := by unfold cut; omega

lemma plusStep_eq_neg_step (d : ℕ) : plusStep (d+1) = -SignedCycleOnes.step d (cut (d+1)) := by
  funext i
  simp only [plusStep, SignedCycleOnes.step, Pi.neg_apply]
  split_ifs <;> norm_num

/-- Literal Q-transpose/all-one identity, not merely a norm comparison. -/
theorem Q_ones_shift (d : ℕ) :
    (SignedReferenceConjugacy.Q (d+1)).transpose.mulVec (fun _ => (1:ℝ)) =
      -((TransitiveOrbit.J d ^ (cut (d+1))).mulVec (fun _ => (1:ℝ))) := by
  rw [Q_transpose_ones, SignedCycleOnes.J_power_ones d (cut (d+1)) (cut_le d)]
  exact plusStep_eq_neg_step d

/-- Every nonnegative integer all-one orbit has equal reference norm.
Dimension zero is included separately, without defining a cyclic shift there. -/
theorem ones_orbit_norm (n r : ℕ) :
    (∑ i : Fin n, ((Kmatrix n ^ r).mulVec (fun _ => (1:ℝ)) i)^2) =
      ∑ i : Fin n, ((TransitiveOrbit.T n ^ r).mulVec (fun _ => (1:ℝ)) i)^2 := by
  cases n with
  | zero => simp
  | succ d =>
    rw [reference_vector_norm, pullback_ones, plusStep_eq_neg_step, Matrix.mulVec_neg]
    simp only [Pi.neg_apply, neg_sq]
    exact SignedCycleOnes.transitive_step_sum_sq d r (cut (d+1)) (cut_le d)
end ReferenceOnesOrbit
#print axioms ReferenceOnesOrbit.Q_ones_shift
#print axioms ReferenceOnesOrbit.ones_orbit_norm
