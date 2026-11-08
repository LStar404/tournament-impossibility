import DiamondFreeDeterminant

noncomputable section
namespace DiamondFreeKernelDeterminant
open Matrix DiamondGap DiamondFreeRepresentation
variable {V K : Type*} [Fintype V] [DecidableEq V] [Field K] [CharZero K]

def signMatrix (T : Tournament V) : Matrix V V K := fun i j => (T.S i j : K)
def kernel (T : Tournament V) (z : K) : Matrix V V K := 1 + z • signMatrix T

/-- Diagonal sign conjugacy preserves the entire finite kernel determinant. -/
theorem kernel_det_switch (T U : Tournament V) (d : V → ℤ)
    (hd : ∀ i, d i ^ 2 = 1)
    (hs : ∀ i j, U.S i j = d i * T.S i j * d j) (z : K) :
    (kernel U z).det = (kernel T z).det := by
  let D : Matrix V V K := diagonal (fun i => (d i : K))
  have hsq (i : V) : (d i : K)^2 = 1 := by exact_mod_cast hd i
  have hDD : D * D = 1 := by
    ext i j
    by_cases hij : i = j
    · subst j
      simpa [D, diagonal_mul, diagonal_apply, pow_two] using hsq i
    · simp [D, diagonal_mul, diagonal_apply, hij, one_apply]
  have hS : signMatrix U = D * signMatrix T * D := by
    ext i j
    simp [signMatrix, D, hs, diagonal_mul, mul_diagonal]
  have hK : kernel U z = D * kernel T z * D := by
    simp only [kernel, hS, mul_add, add_mul, mul_one, hDD,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  have hdet : D.det * D.det = 1 := by rw [← det_mul, hDD, det_one]
  rw [hK, det_mul, det_mul]
  calc
    _ = D.det * D.det * (kernel T z).det := by ring
    _ = _ := by rw [hdet, one_mul]

/-- Actual zero-diamond determinant over any characteristic-zero field.
No principal-minor or spectral hypothesis is an input. -/
theorem diamondFree_kernel_det (T : Tournament V) (hT : DiamondFree T) (z : K) :
    (kernel T z).det =
      ((1+z)^(Fintype.card V) + (1-z)^(Fintype.card V))/2 := by
  obtain ⟨d,U,hd,hs,ht⟩ := exists_transitive_switch T hT
  obtain ⟨e,he⟩ := ColorTransport.transitive_tournament_enumeration U ht
  have hsign : (signMatrix U : Matrix V V K).submatrix e e =
      TournamentHamiltonian.transitiveSkew (Fintype.card V) := by
    ext i j
    have hr := he i j
    simp only [ColorTransport.orderSign] at hr
    change (U.S (e i) (e j) : K) = _
    unfold TournamentHamiltonian.transitiveSkew
    by_cases hij : i < j
    · simp [hij] at hr ⊢
      exact_mod_cast hr
    · by_cases hji : j < i
      · simp [hij, hji] at hr ⊢
        exact_mod_cast hr
      · simp [hij, hji] at hr ⊢
        exact_mod_cast hr
  have hker : (kernel U z).submatrix e e =
      TournamentHamiltonian.transitiveKernel (Fintype.card V) z := by
    simp [kernel, TournamentHamiltonian.transitiveKernel, submatrix_add,
      submatrix_smul, submatrix_one_equiv, hsign]
  calc
    _ = (kernel U z).det := (kernel_det_switch T U d hd hs z).symm
    _ = ((kernel U z).submatrix e e).det := (det_submatrix_equiv_self e _).symm
    _ = _ := by rw [hker, TournamentHamiltonian.transitiveKernel_det]

theorem zero_diamonds_kernel_det (T : Tournament V) (hT : T.diamonds.card = 0) (z : K) :
    (kernel T z).det =
      ((1+z)^(Fintype.card V) + (1-z)^(Fintype.card V))/2 :=
  diamondFree_kernel_det T (diamondFree_of_card_zero T hT) z

/-- The minus-sign parameterization has the same even finite polynomial.
For real z/n this is the cosh, not the cos, scaling. -/
theorem zero_diamonds_normalized_det {n : ℕ} (T : Tournament (Fin n))
    (hT : T.diamonds.card = 0) (z : K) :
    ((1 : Matrix (Fin n) (Fin n) K) - (z/(n : K)) • signMatrix T).det =
      ((1+z/(n : K))^n+(1-z/(n : K))^n)/2 := by
  have h := zero_diamonds_kernel_det T hT (-(z/(n : K)))
  simpa only [kernel, neg_smul, sub_eq_add_neg, Fintype.card_fin,
    neg_neg, add_comm] using h
end DiamondFreeKernelDeterminant
#print axioms DiamondFreeKernelDeterminant.zero_diamonds_kernel_det
#print axioms DiamondFreeKernelDeterminant.zero_diamonds_normalized_det
