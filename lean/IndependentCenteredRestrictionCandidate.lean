import PermanentCircleActualCentering

/-! Verified in the 557-module direct-Lean compilation and declaration audit. Independent (not necessarily principal) restriction.
Selection matrices, their norms, and centered transport are proved rather
than supplied as hypotheses. Uses the rectangular L2 operator matrix norm. -/
set_option autoImplicit false
noncomputable section
namespace IndependentCenteredRestrictionCandidate
open Matrix Finset
open scoped Matrix.Norms.L2Operator
open PermanentSpectralFrame
variable {n m : ℕ}

def selection (e : Fin m ↪ Fin n) : Matrix (Fin n) (Fin m) ℂ :=
  fun i j => if i=e j then 1 else 0

def proj (k : ℕ) : Matrix (Fin k) (Fin k) ℂ := 1-averaging k

lemma selection_gram (e : Fin m ↪ Fin n) :
    (selection e)ᴴ * selection e = 1 := by
  ext i j
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, selection,
    Matrix.one_apply, e.injective.eq_iff, eq_comm]

lemma selection_norm (e : Fin m ↪ Fin n) : ‖selection e‖ ≤ 1 := by
  have hh := Matrix.l2_opNorm_conjTranspose_mul_self (selection e)
  rw [selection_gram] at hh
  have hi : ‖(1 : Matrix (Fin m) (Fin m) ℂ)‖ ≤ 1 := by
    rw [← Matrix.l2_opNorm_toEuclideanCLM, map_one]
    exact ContinuousLinearMap.norm_id_le
  have hn := norm_nonneg (selection e)
  nlinarith

lemma proj_norm (hm : 0 < m) : ‖proj m‖ ≤ 1 := by
  change ‖(1-averaging m : Matrix (Fin m) (Fin m) ℂ)‖ ≤ 1
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  exact complement_op_norm_le_one hm

lemma averaging_selection (e : Fin m ↪ Fin n) :
    averaging n * selection e = Matrix.of (fun _ _ => (n:ℂ)⁻¹) := by
  ext i j
  simp [Matrix.mul_apply, averaging, selection]

lemma averaging_selection_proj (hm : 0 < m) (e : Fin m ↪ Fin n) :
    averaging n * selection e * proj m = 0 := by
  rw [averaging_selection]
  change (Matrix.of (fun _ _ => (n:ℂ)⁻¹) : Matrix (Fin n) (Fin m) ℂ) * proj m = 0
  unfold proj
  rw [Matrix.mul_sub, Matrix.mul_one]
  have hh : (Matrix.of (fun (_ : Fin n) (_ : Fin m) => (n:ℂ)⁻¹)) * averaging m =
      (Matrix.of (fun (_ : Fin n) (_ : Fin m) => (n:ℂ)⁻¹)) := by
    ext i j
    have hm0 : (m:ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
    simp only [Matrix.mul_apply, averaging, Matrix.of_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  rw [hh, sub_self]

lemma centered_extension (hm : 0 < m) (e : Fin m ↪ Fin n) :
    proj n * selection e * proj m = selection e * proj m := by
  rw [proj, Matrix.sub_mul, Matrix.one_mul, Matrix.sub_mul,
    averaging_selection_proj hm e, sub_zero]

lemma centered_restriction (hm : 0 < m) (e : Fin m ↪ Fin n) :
    proj m * (selection e)ᴴ * proj n = proj m * (selection e)ᴴ := by
  have hh := congrArg Matrix.conjTranspose (centered_extension hm e)
  simpa [Matrix.conjTranspose_mul, proj, averaging_adjoint, Matrix.mul_assoc] using hh

lemma selection_submatrix (A : Matrix (Fin n) (Fin n) ℂ)
    (e f : Fin m ↪ Fin n) :
    (selection e)ᴴ * A * selection f = A.submatrix e f := by
  ext i j
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, selection, Matrix.submatrix]

/-- The two injections may be entirely different. -/
theorem independent_centering_identity (hm : 0 < m)
    (A : Matrix (Fin n) (Fin n) ℂ) (e f : Fin m ↪ Fin n) :
    proj m * A.submatrix e f * proj m =
      (proj m * (selection e)ᴴ) * (proj n*A*proj n) * (selection f*proj m) := by
  rw [← selection_submatrix A e f]
  have hl := centered_restriction hm e
  have hr := centered_extension hm f
  calc
    _ = (proj m*(selection e)ᴴ)*A*(selection f*proj m) := by simp only [Matrix.mul_assoc]
    _ = ((proj m*(selection e)ᴴ)*proj n)*A*(proj n*selection f*proj m) := by rw [hl, hr]
    _ = _ := by simp only [Matrix.mul_assoc]

/-- Closed finite operator estimate, not a scaling or extremality theorem. -/
theorem independent_centered_norm (hm : 0 < m)
    (A : Matrix (Fin n) (Fin n) ℂ) (e f : Fin m ↪ Fin n) :
    ‖proj m * A.submatrix e f * proj m‖ ≤ ‖proj n*A*proj n‖ := by
  rw [independent_centering_identity hm A e f]
  have hl : ‖proj m*(selection e)ᴴ‖ ≤ 1 := by
    calc
      _ ≤ ‖proj m‖*‖(selection e)ᴴ‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ 1*1 := by
        rw [Matrix.l2_opNorm_conjTranspose]
        exact mul_le_mul (proj_norm hm) (selection_norm e) (norm_nonneg _) (by norm_num)
      _ = 1 := by ring
  have hr : ‖selection f*proj m‖ ≤ 1 := by
    calc
      _ ≤ ‖selection f‖*‖proj m‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ 1*1 := by
        exact mul_le_mul (selection_norm f) (proj_norm hm) (norm_nonneg _) (by norm_num)
      _ = 1 := by ring
  calc
    _ ≤ (‖proj m*(selection e)ᴴ‖*‖proj n*A*proj n‖)*‖selection f*proj m‖ :=
      (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ (1*‖proj n*A*proj n‖)*1 := by gcongr
    _ = _ := by ring

end IndependentCenteredRestrictionCandidate
