import PermanentSpectralFrame

/-! Concrete factors, no assumed factorization premise. -/
noncomputable section
namespace PermanentSpectralFrame
open Matrix
variable {n : ℕ}

lemma frame_star_mul (A : Matrix (Fin n) (Fin n) ℂ) :
    (frame A : Matrix (Fin n) (Fin n) ℂ)ᴴ * frame A=1 := by
  simpa [Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self (frame A)

lemma frame_mul_star (A : Matrix (Fin n) (Fin n) ℂ) :
    (frame A : Matrix (Fin n) (Fin n) ℂ) * (frame A : Matrix (Fin n) (Fin n) ℂ)ᴴ=1 := by
  simpa [Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self (frame A)

lemma frame_gram (A : Matrix (Fin n) (Fin n) ℂ) :
    (frame A : Matrix (Fin n) (Fin n) ℂ)ᴴ * (Aᴴ*A) * frame A =
      diagonal (fun i => (eigenvalue A i : ℂ)) := by
  change (frame A : Matrix (Fin n) (Fin n) ℂ)ᴴ * gram A * frame A = _
  rw [spectral_representation]
  simp only [← Matrix.mul_assoc,frame_star_mul,one_mul]
  simp only [Matrix.mul_assoc,frame_star_mul,mul_one]

lemma fourthRoot_zero_imp (A : Matrix (Fin n) (Fin n) ℂ) (i : Fin n)
    (hd : fourthRoot A i=0) : eigenvalue A i=0 := by
  have hs := fourthRoot_sq A i
  have hl := singularRoot_sq A i
  rw [hd,zero_pow (by decide : 2≠0)] at hs
  rw [← hs,zero_pow (by decide : 2≠0)] at hl
  exact hl.symm

lemma factor_scalar (A : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    (fourthRoot A i : ℂ)⁻¹ * (eigenvalue A i : ℂ) *
      (fourthRoot A i : ℂ)⁻¹ = (singularRoot A i : ℂ) := by
  have hd : (fourthRoot A i : ℂ)^2=(singularRoot A i : ℂ) := by
    exact_mod_cast fourthRoot_sq A i
  have hs : (singularRoot A i : ℂ)^2=(eigenvalue A i : ℂ) := by
    exact_mod_cast singularRoot_sq A i
  by_cases hz : (fourthRoot A i : ℂ)=0
  · rw [hz,zero_pow (by decide : 2≠0)] at hd
    simp [hz,← hd]
  · rw [← hs,← hd]
    field_simp
    <;> ring

/-- Zero eigenvalue columns are killed by A, so the totalized inverse in the
fourth-root diagonal reconstructs A without any nonsingularity assumption. -/
lemma supported_columns (A : Matrix (Fin n) (Fin n) ℂ) :
    A * frame A * diagonal (fun i => (fourthRoot A i : ℂ)⁻¹ * (fourthRoot A i : ℂ)) =
      A * frame A := by
  ext i j
  rw [Matrix.mul_diagonal]
  by_cases hd : (fourthRoot A j : ℂ)=0
  · have hdR : fourthRoot A j=0 := by exact_mod_cast hd
    have hz := zero_eigenvalue_column A j (fourthRoot_zero_imp A j hdR)
    have hc : (A * frame A) i j=0 := congrFun hz i
    simp [hd,hc]
  · rw [inv_mul_cancel₀ hd,mul_one]

/-- Concrete construction from the actual Gram spectrum. -/
theorem factors_reconstruct (A : Matrix (Fin n) (Fin n) ℂ) :
    leftFactor A * (rightFactor A)ᴴ = A := by
  unfold leftFactor rightFactor
  rw [Matrix.conjTranspose_mul]
  have hD : (diagonal (fun i => (fourthRoot A i : ℂ)))ᴴ =
      diagonal (fun i => (fourthRoot A i : ℂ)) := by ext i j; by_cases hij : i=j <;> simp [Matrix.conjTranspose_apply, Matrix.diagonal_apply, hij, Ne.symm]
  rw [hD]
  calc
    _ = (A * frame A * diagonal (fun i =>
        (fourthRoot A i : ℂ)⁻¹*(fourthRoot A i : ℂ))) *
          (frame A : Matrix (Fin n) (Fin n) ℂ)ᴴ := by
      rw [← Matrix.diagonal_mul_diagonal]
      simp only [Matrix.mul_assoc]
    _ = (A * frame A) * (frame A : Matrix (Fin n) (Fin n) ℂ)ᴴ := by rw [supported_columns]
    _ = A := by rw [Matrix.mul_assoc,frame_mul_star,mul_one]

theorem rightFactor_gram (A : Matrix (Fin n) (Fin n) ℂ) :
    (rightFactor A)ᴴ * rightFactor A = diagonal (fun i => (singularRoot A i : ℂ)) := by
  have hD : (diagonal (fun i => (fourthRoot A i : ℂ)))ᴴ =
      diagonal (fun i => (fourthRoot A i : ℂ)) := by ext i j; by_cases hij : i=j <;> simp [Matrix.conjTranspose_apply, Matrix.diagonal_apply, hij, Ne.symm]
  unfold rightFactor
  rw [Matrix.conjTranspose_mul,hD]
  calc
    _ = diagonal (fun i => (fourthRoot A i : ℂ)) *
        ((frame A : Matrix (Fin n) (Fin n) ℂ)ᴴ * frame A) *
        diagonal (fun i => (fourthRoot A i : ℂ)) := by simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [frame_star_mul,mul_one,Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      simpa only [pow_two] using (show (fourthRoot A i : ℂ)^2=(singularRoot A i : ℂ) by
        exact_mod_cast fourthRoot_sq A i)

theorem leftFactor_gram (A : Matrix (Fin n) (Fin n) ℂ) :
    (leftFactor A)ᴴ * leftFactor A = diagonal (fun i => (singularRoot A i : ℂ)) := by
  have hD : (diagonal (fun i => (fourthRoot A i : ℂ)⁻¹))ᴴ =
      diagonal (fun i => (fourthRoot A i : ℂ)⁻¹) := by ext i j; by_cases hij : i=j <;> simp [Matrix.conjTranspose_apply, Matrix.diagonal_apply, hij, Ne.symm]
  unfold leftFactor
  simp only [Matrix.conjTranspose_mul,hD]
  calc
    _ = diagonal (fun i => (fourthRoot A i : ℂ)⁻¹) *
        ((frame A : Matrix (Fin n) (Fin n) ℂ)ᴴ * (Aᴴ*A) * frame A) *
        diagonal (fun i => (fourthRoot A i : ℂ)⁻¹) := by simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [frame_gram,Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      exact factor_scalar A i
end PermanentSpectralFrame
#print axioms PermanentSpectralFrame.factors_reconstruct
#print axioms PermanentSpectralFrame.leftFactor_gram
#print axioms PermanentSpectralFrame.rightFactor_gram
