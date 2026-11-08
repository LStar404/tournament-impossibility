import Mathlib

noncomputable section
open Matrix WithLp
namespace MatrixEuclideanEntryBound

/-- Frobenius norm named explicitly, to avoid confusing it with the entrywise
or operator norm instances on matrices. -/
def frobenius {ι κ : Type*} [Fintype ι] [Fintype κ] (M : Matrix ι κ ℂ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, ‖M i j‖^2)

section OperatorBridge
attribute [local instance] Matrix.frobeniusNormedAddCommGroup
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Euclidean operator norm is bounded by the explicitly named Frobenius norm. -/
theorem operator_le_frobenius (M : Matrix ι ι ℂ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) M‖ ≤ frobenius M := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro x
  have hm := Matrix.frobenius_norm_mul M (Matrix.replicateCol Unit (ofLp x))
  have he : M * Matrix.replicateCol Unit (ofLp x) =
      Matrix.replicateCol Unit (M *ᵥ ofLp x) := by
    ext i j
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [he, Matrix.frobenius_norm_replicateCol,
    Matrix.frobenius_norm_replicateCol] at hm
  simpa [frobenius, Matrix.frobenius_norm_def, Real.rpow_two,
    Real.sqrt_eq_rpow, ← Matrix.ofLp_toEuclideanCLM] using hm
end OperatorBridge

/-- An n by n error with every entry bounded by C/n has Frobenius norm at
most C. No zero-diagonal assumption is needed. -/
theorem frobenius_le_of_entries {n : ℕ} (hn : 0<n) (M : Matrix (Fin n) (Fin n) ℂ)
    {C : ℝ} (hC : 0≤C) (hentry : ∀ i j, ‖M i j‖≤C/(n:ℝ)) :
    frobenius M ≤ C := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  apply Real.sqrt_le_iff.mpr
  refine ⟨hC, ?_⟩
  calc
    ∑ i, ∑ j, ‖M i j‖^2 ≤ ∑ i : Fin n, ∑ j : Fin n, (C/(n:ℝ))^2 := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact (sq_le_sq₀ (norm_nonneg _) (div_nonneg hC hnR.le)).mpr (hentry i j)
    _ = C^2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp [ne_of_gt hnR]

theorem operator_le_of_entries {n : ℕ} (hn : 0<n) (M : Matrix (Fin n) (Fin n) ℂ)
    {C : ℝ} (hC : 0≤C) (hentry : ∀ i j, ‖M i j‖≤C/(n:ℝ)) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) M‖ ≤ C :=
  (operator_le_frobenius M).trans (frobenius_le_of_entries hn M hC hentry)

/-- Split the scalar identity before estimating the error; applying a Frobenius
bound to the entire matrix would introduce an unnecessary sqrt(n). -/
theorem scalar_identity_add_error {n : ℕ} (hn : 0<n)
    (d : ℂ) (E : Matrix (Fin n) (Fin n) ℂ) {D C : ℝ}
    (hd : ‖d‖≤D) (hC : 0≤C) (hentry : ∀ i j, ‖E i j‖≤C/(n:ℝ)) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (d • (1 : Matrix (Fin n) (Fin n) ℂ) + E)‖ ≤ D+C := by
  rw [map_add, map_smul, map_one]
  calc
    _ ≤ ‖d • (1 : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))‖ +
        ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) E‖ := norm_add_le _ _
    _ ≤ D+C := by
      apply add_le_add _ (operator_le_of_entries hn E hC hentry)
      rw [norm_smul]
      exact (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg d)).trans
        (by simpa using hd)

end MatrixEuclideanEntryBound
#print axioms MatrixEuclideanEntryBound.operator_le_frobenius
#print axioms MatrixEuclideanEntryBound.scalar_identity_add_error
