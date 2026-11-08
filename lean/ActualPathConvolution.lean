import TournamentHamiltonian.PathConvolutionGenerating
import TournamentSequence

/-! Exact S1 normalization, transferred from the generic marked-cycle proof.
No asymptotic or path-convolution hypothesis occurs in these statements. -/
namespace TournamentHamiltonian
open scoped Classical

noncomputable def pathWeightMatrix {n : ℕ} (T : Tournament n) :
    Matrix (Fin n) (Fin n) ℝ := Matrix.of (fun _ _ => 1) + signMatrix T

theorem pathWeightMatrix_offdiag {n : ℕ} (T : Tournament n)
    {i j : Fin n} (h : i ≠ j) :
    pathWeightMatrix T i j = 2 * adjacency T i j := by
  have hh := twice_adjacency T i j
  simpa [pathWeightMatrix, h] using hh.symm

theorem weighted_path_sum {n : ℕ} (T : Tournament (n + 1)) :
    (∑ σ : Equiv.Perm (Fin (n + 1)),
      ∏ i : Fin n, pathWeightMatrix T (σ i.castSucc) (σ i.succ)) =
      (2 : ℝ)^n * (pathCount T : ℝ) := by
  rw [pathCount_eq_sum_consecutive_product, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  have hn (i : Fin n) : σ i.castSucc ≠ σ i.succ := by
    intro h
    have := congrArg Fin.val (σ.injective h)
    simp only [Fin.val_castSucc, Fin.val_succ] at this
    omega
  simp_rw [pathWeightMatrix_offdiag T (hn _)]
  rw [Finset.prod_mul_distrib]
  simp

theorem actual_path_convolution_all_subsets {n : ℕ} (T : Tournament (n + 1)) :
    (2 : ℝ)^n * (pathCount T : ℝ) =
      ∑ U : Finset (Fin (n + 1)),
        ((signMatrix T).submatrix (Subtype.val : U → Fin (n + 1)) Subtype.val).det *
        ((pathWeightMatrix T).submatrix
          (Subtype.val : (Uᶜ : Finset (Fin (n + 1))) → Fin (n + 1))
          Subtype.val).permanent := by
  have h := complement_det_per_convolution_bool_eq_cycles (pathWeightMatrix T)
  rw [← det_per_subset_sum_eq_bool] at h
  have hd (U : Finset (Fin (n + 1))) :
      ((Matrix.of (fun _ _ => (1 : ℝ)) - pathWeightMatrix T).submatrix
        (Subtype.val : U → Fin (n + 1)) Subtype.val).det =
      ((signMatrix T).submatrix (Subtype.val : U → Fin (n + 1)) Subtype.val).det := by
    have hm : (Matrix.of (fun _ _ => (1 : ℝ)) - pathWeightMatrix T).submatrix
        (Subtype.val : U → Fin (n + 1)) Subtype.val =
        ((signMatrix T).submatrix (Subtype.val : U → Fin (n + 1)) Subtype.val).transpose := by
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.sub_apply,
        pathWeightMatrix, Matrix.add_apply, Matrix.of_apply]
      have hs := signMatrix_skew T i.val j.val
      linarith
    rw [hm, Matrix.det_transpose]
  simp_rw [hd] at h
  simpa only [Fintype.card_fin, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
    ite_false, zero_add, ← sum_path_products_eq_marked_cycles,
    weighted_path_sum] using h.symm

theorem odd_sign_principal_det_zero {n : ℕ} (T : Tournament n)
    (U : Finset (Fin n)) (h : ¬Even U.card) :
    ((signMatrix T).submatrix (Subtype.val : U → Fin n) Subtype.val).det = 0 := by
  let M : Matrix U U ℝ := (signMatrix T).submatrix (Subtype.val : U → Fin n) Subtype.val
  have ht : M.transpose = -M := by
    ext i j
    exact signMatrix_skew T j.val i.val
  have hd := Matrix.det_transpose M
  rw [ht, Matrix.det_neg] at hd
  have ho : Odd (Fintype.card U) := by
    simpa using (Nat.not_even_iff_odd.mp h)
  rw [ho.neg_one_pow] at hd
  change M.det = 0
  linarith

/-- Supplement S1, with precisely the even-subset restriction and 2^(n-1)
normalization (the positive order is written n+1 to avoid truncated subtraction). -/
theorem actual_path_convolution_even_subsets {n : ℕ} (T : Tournament (n + 1)) :
    (2 : ℝ)^n * (pathCount T : ℝ) =
      ∑ U : Finset (Fin (n + 1)), if Even U.card then
        ((signMatrix T).submatrix (Subtype.val : U → Fin (n + 1)) Subtype.val).det *
        ((pathWeightMatrix T).submatrix
          (Subtype.val : (Uᶜ : Finset (Fin (n + 1))) → Fin (n + 1))
          Subtype.val).permanent else 0 := by
  rw [actual_path_convolution_all_subsets]
  apply Finset.sum_congr rfl
  intro U _
  by_cases h : Even U.card
  · simp [h]
  · simp [h, odd_sign_principal_det_zero T U h]

end TournamentHamiltonian

namespace NonAlgebraicity
/-- Exact conversion of this repository's finite tournament encoding. -/
def asPathTournament {n : ℕ} (o : Orientation n) : TournamentHamiltonian.Tournament n :=
  ⟨edge o, ⟨edge_irrefl o, fun _ _ h => edge_opposite o h⟩⟩

@[simp] theorem pathCount_asPathTournament {n : ℕ} (o : Orientation n) :
    TournamentHamiltonian.pathCount (asPathTournament o) = hamiltonianPathCount o := rfl

/-- S1 for the very same path-count function used by the main application. -/
theorem hamiltonianPathCount_convolution {n : ℕ} (o : Orientation (n + 1)) :
    (2 : ℝ)^n * (hamiltonianPathCount o : ℝ) =
      ∑ U : Finset (Fin (n + 1)), if Even U.card then
        ((TournamentHamiltonian.signMatrix (asPathTournament o)).submatrix
          (Subtype.val : U → Fin (n + 1)) Subtype.val).det *
        ((TournamentHamiltonian.pathWeightMatrix (asPathTournament o)).submatrix
          (Subtype.val : (Uᶜ : Finset (Fin (n + 1))) → Fin (n + 1))
          Subtype.val).permanent else 0 :=
  TournamentHamiltonian.actual_path_convolution_even_subsets (asPathTournament o)
end NonAlgebraicity
