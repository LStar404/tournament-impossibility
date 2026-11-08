import SignedReferenceConjugacy
import SignedConjugacy
import TransitiveOrbit
import KMatrixIdentification
import BasisReference
noncomputable section
namespace ReferenceMomentComparison
open Finset Matrix ReferenceDiagonal ZigzagReference TournamentPowerComparison
open IteratedVectorMajorization TournamentSwitching

lemma T_transpose (n : ℕ) : (Tmatrix n).transpose = -(Tmatrix n) := by
  ext i j
  exact ReferenceSquare.T_skew j.val i.val

lemma K_normal (n : ℕ) : Commute (Kmatrix n).transpose (Kmatrix n) := by
  rw [Kmatrix_symmetric]
lemma T_normal (n : ℕ) : Commute (Tmatrix n).transpose (Tmatrix n) := by
  rw [T_transpose]
  show (-(Tmatrix n)) * Tmatrix n = Tmatrix n * (-(Tmatrix n))
  simp

/-- Actual K and T reference-column norm identity, with no assumed conjugacy. -/
theorem reference_column_norm (n r : ℕ) (j : Fin n) :
    (∑ i : Fin n, ((Kmatrix n ^ r) i j)^2) =
      ∑ i : Fin n, ((Tmatrix n ^ r) i (perm n j))^2 := by
  apply SignedConjugacy.column_sq_of_gram_conjugacy
    (Kmatrix n) (Tmatrix n) (K_normal n) (T_normal n)
    (perm n) (fun i => sigma i.val) (fun i => sigma_sq i.val)
  intro i l
  rw [Kmatrix_symmetric, T_transpose]
  simpa only [pow_two, neg_mul] using SignedReferenceConjugacy.concrete_entry n i l

lemma perm_first (m : ℕ) : perm (m+1) (0 : Fin (m+1)) = 0 := by
  apply Fin.ext
  simp [perm, position]

lemma reference_first_column (m r : ℕ) :
    (∑ i : Fin (m+1), ((Kmatrix (m+1) ^ r) i 0)^2) =
      TransitiveOrbit.columnSq ((TransitiveOrbit.T (m+1))^r) 0 := by
  have h := reference_column_norm (m+1) r (0 : Fin (m+1))
  rw [perm_first] at h
  exact h

lemma comparison_basis_norm (m r : ℕ) :
    (∑ i ∈ range (m+1), (comparison (m+1) (sortedPad (basis (0 : Fin (m+1)))) r i)^2) =
      TransitiveOrbit.columnSq ((TransitiveOrbit.T (m+1))^r) 0 := by
  have hz : (fun j : Fin (m+1) => sortedPad (basis (0 : Fin (m+1))) j.val) =
      basis (0 : Fin (m+1)) := by
    funext j
    exact BasisReference.sortedPad_basis_restrict (m+1) (by omega) j
  calc
    _ = ∑ i : Fin (m+1), (comparison (m+1) (sortedPad (basis (0 : Fin (m+1)))) r i.val)^2 :=
      (Fin.sum_univ_eq_sum_range _ _).symm
    _ = ∑ i : Fin (m+1), ((Kmatrix (m+1)^r) i 0)^2 := by
      apply sum_congr rfl
      intro i hi
      rw [KMatrixIdentification.comparison_power, hz]
      rw [show KMatrixIdentification.matrix (m+1) = Kmatrix (m+1) from rfl]
      simp [basis]
    _ = _ := reference_first_column m r

/-- All nonnegative integer matrix moments: the actual squared Frobenius
norm is maximized by the transitive sign matrix. Includes dimension zero. -/
theorem frobenius_all_powers (n r : ℕ) (B : VectorWeakMajorization.Tournament n) :
    (∑ i : Fin n, ∑ j : Fin n, ((TournamentPowerComparison.matrix B ^ r) i j)^2) ≤
      ∑ i : Fin n, ∑ j : Fin n, ((TransitiveOrbit.T n ^ r) i j)^2 := by
  cases n with
  | zero => simp
  | succ m =>
    have h := frobenius_power_bound B (0 : Fin (m+1)) r
    rw [comparison_basis_norm] at h
    rw [TransitiveOrbit.power_frobenius]
    rw [sum_comm]
    exact h
end ReferenceMomentComparison
#print axioms ReferenceMomentComparison.reference_column_norm
#print axioms ReferenceMomentComparison.frobenius_all_powers
