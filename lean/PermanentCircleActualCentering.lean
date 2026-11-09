import PermanentCircleCentering
import MatrixEuclideanEntryBound

/-! Draft: actual averaging projection and score-controlled centering.
No compilation claim accompanies this source. -/
noncomputable section
namespace PermanentSpectralFrame
open Matrix
variable {n : ℕ}

lemma averaging_op_adjoint : (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (averaging n)).adjoint = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (averaging n) := by
  rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star]
  exact congrArg (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)) (averaging_adjoint n)

lemma averaging_op_square (hn : 0 < n) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (averaging n) * Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (averaging n) = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (averaging n) := by
  rw [← map_mul, averaging_square hn]

lemma complement_square (hn : 0 < n) :
    (1 - averaging n) * (1 - averaging n) = 1 - averaging n := by
  simp only [sub_mul, mul_sub, one_mul, mul_one, averaging_square hn]
  abel

lemma complement_adjoint : (1 - averaging n)ᴴ = 1 - averaging n := by
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, averaging_adjoint]

lemma averaging_op_norm_le_one (hn : 0 < n) : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (averaging n)‖ ≤ 1 := by
  simpa using orthogonal_block_contraction (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (averaging n)) 0
    averaging_op_adjoint (averaging_op_square hn) (by simp) (by simp) (by simp)

lemma complement_op_norm_le_one (hn : 0 < n) : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (1 - averaging n)‖ ≤ 1 := by
  have hs : (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (1 - averaging n)).adjoint = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (1 - averaging n) := by
    rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star]
    exact congrArg (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)) complement_adjoint
  have hi : Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (1 - averaging n) * Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (1 - averaging n) = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (1 - averaging n) := by
    rw [← map_mul, complement_square hn]
  simpa using orthogonal_block_contraction (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (1 - averaging n)) 0
    hs hi (by simp) (by simp) (by simp)

lemma averaging_mul_entry (M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (averaging n * M) i j = (n : ℂ)⁻¹ * ∑ k, M k j := by
  simp [Matrix.mul_apply, averaging, Finset.mul_sum]

lemma mul_averaging_entry (M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (M * averaging n) i j = (∑ k, M i k) * (n : ℂ)⁻¹ := by
  simp [Matrix.mul_apply, averaging, Finset.sum_mul]

lemma averaging_mul_bound (hn : 0 < n) (M : Matrix (Fin n) (Fin n) ℂ)
    {K : ℝ} (hK : 0 ≤ K) (hcol : ∀ j, ‖∑ i, M i j‖ ≤ K / n) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (averaging n * M)‖ ≤ K / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  apply MatrixEuclideanEntryBound.operator_le_of_entries hn _ (div_nonneg hK hnR.le)
  intro i j
  rw [averaging_mul_entry, norm_mul, norm_inv]
  have hnc : ‖(n : ℂ)‖ = (n : ℝ) := by simp
  rw [hnc]
  calc
    (n : ℝ)⁻¹ * ‖∑ k, M k j‖ ≤ (n : ℝ)⁻¹ * (K / n) :=
      mul_le_mul_of_nonneg_left (hcol j) (inv_nonneg.mpr hnR.le)
    _ = (K / n) / n := by ring

lemma mul_averaging_bound (hn : 0 < n) (M : Matrix (Fin n) (Fin n) ℂ)
    {K : ℝ} (hK : 0 ≤ K) (hrow : ∀ i, ‖∑ j, M i j‖ ≤ K / n) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (M * averaging n)‖ ≤ K / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  apply MatrixEuclideanEntryBound.operator_le_of_entries hn _ (div_nonneg hK hnR.le)
  intro i j
  rw [mul_averaging_entry, norm_mul, norm_inv]
  have hnc : ‖(n : ℂ)‖ = (n : ℝ) := by simp
  rw [hnc]
  simpa only [div_eq_mul_inv] using
    mul_le_mul_of_nonneg_right (hrow i) (inv_nonneg.mpr hnR.le)

/-- Actual entrywise row and column score bounds imply the sharp O(1/n)
centering error in Euclidean operator norm. -/
theorem actual_centering_error (hn : 0 < n) (M : Matrix (Fin n) (Fin n) ℂ)
    {K : ℝ} (hK : 0 ≤ K)
    (hrow : ∀ i, ‖∑ j, M i j‖ ≤ K / n)
    (hcol : ∀ j, ‖∑ i, M i j‖ ≤ K / n) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (M - centered M)‖ ≤ 2 * K / n := by
  rw [centering_residual, map_add]
  have hrest : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) ((1 - averaging n) * M * averaging n)‖ ≤ K / n := by
    rw [Matrix.mul_assoc, map_mul]
    calc
      _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (1 - averaging n)‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (M * averaging n)‖ := norm_mul_le _ _
      _ ≤ 1 * (K / n) := mul_le_mul (complement_op_norm_le_one hn)
        (mul_averaging_bound hn M hK hrow) (norm_nonneg _)
        (by norm_num)
      _ = K / n := one_mul _
  calc
    _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (averaging n * M)‖ + ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) ((1 - averaging n) * M * averaging n)‖ := norm_add_le _ _
    _ ≤ K / n + K / n := add_le_add (averaging_mul_bound hn M hK hcol) hrest
    _ = 2 * K / n := by ring

lemma centered_op_bound (hn : 0 < n) (M : Matrix (Fin n) (Fin n) ℂ)
    {q : ℝ} (hM : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) M‖ ≤ q) : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (centered M)‖ ≤ q := by
  unfold centered
  simp only [map_mul]
  calc
    _ ≤ (‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (1 - averaging n)‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) M‖) * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (1 - averaging n)‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1 * q) * 1 := mul_le_mul
      (mul_le_mul (complement_op_norm_le_one hn) hM (norm_nonneg _) (by norm_num))
      (complement_op_norm_le_one hn) (norm_nonneg _) (by linarith [norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) M)])
    _ = q := by ring

lemma actual_centered_circle_contraction (hn : 0 < n)
    (M : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) {T q : ℝ}
    (hT : 0 ≤ T) (hq : 0 ≤ q) (hz : ‖z‖ ≤ T)
    (hM : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) M‖ ≤ q) (hTq : T * q ≤ 1) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (averaging n + z • centered M)‖ ≤ 1 := by
  rw [map_add, map_smul]
  apply orthogonal_block_contraction (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (averaging n)) (z • Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (centered M))
    averaging_op_adjoint (averaging_op_square hn)
  · rw [mul_smul_comm, ← map_mul, centered_left_zero hn, map_zero, smul_zero]
  · rw [smul_mul_assoc, ← map_mul, centered_right_zero hn, map_zero, smul_zero]
  · rw [norm_smul]
    exact (mul_le_mul hz (centered_op_bound hn M hM) (norm_nonneg _) hT).trans hTq

/-- Sharp top singular-value control from actual scores, uniformly in z. -/
theorem actual_circle_operator_bound (hn : 0 < n)
    (M : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) {K T q : ℝ}
    (hK : 0 ≤ K) (hT : 0 ≤ T) (hq : 0 ≤ q)
    (hrow : ∀ i, ‖∑ j, M i j‖ ≤ K / n)
    (hcol : ∀ j, ‖∑ i, M i j‖ ≤ K / n)
    (hz : ‖z‖ ≤ T) (hM : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) M‖ ≤ q) (hTq : T * q ≤ 1) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (averaging n + z • M)‖ ≤ 1 + 2 * T * K / n := by
  have he : averaging n + z • M =
      (averaging n + z • centered M) + z • (M - centered M) := by
    rw [smul_sub]
    abel
  rw [he, map_add, map_smul]
  calc
    _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (averaging n + z • centered M)‖ + ‖z • Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (M - centered M)‖ := norm_add_le _ _
    _ ≤ 1 + T * (2 * K / n) := by
      apply add_le_add (actual_centered_circle_contraction hn M z hT hq hz hM hTq)
      rw [norm_smul]
      exact mul_le_mul hz (actual_centering_error hn M hK hrow hcol) (norm_nonneg _) hT
    _ = 1 + 2 * T * K / n := by ring
end PermanentSpectralFrame
#print axioms PermanentSpectralFrame.actual_centering_error
#print axioms PermanentSpectralFrame.actual_circle_operator_bound
