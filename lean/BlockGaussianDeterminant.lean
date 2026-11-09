import GaussianDeterminantBranch

noncomputable section
namespace BlockGaussianDeterminant
open Matrix DiamondGap DiamondFreeKernelDeterminant DiamondFreeComplexResolvent
open GaussianParameterBranch GaussianDeterminantBranch

def interaction {n : ℕ} (T : Tournament (Fin n)) (v : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (n : ℂ)⁻¹ • (signMatrix T + v • 1)

def blockQ {n : ℕ} (T : Tournament (Fin n)) (v : ℂ) :=
  Matrix.fromBlocks 0 (interaction T v) (interaction T v).transpose 0

def blockMatrix {n : ℕ} (T : Tournament (Fin n)) (v z : ℂ) :=
  Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ)
    ((z/(n:ℂ)) • (signMatrix T + v • 1))
    ((z/(n:ℂ)) • (-signMatrix T + v • 1)) 1

lemma sign_transpose {n : ℕ} (T : Tournament (Fin n)) :
    (signMatrix T : Matrix (Fin n) (Fin n) ℂ).transpose = -signMatrix T := by
  ext i j
  change (T.S j i : ℂ) = -(T.S i j : ℂ)
  exact_mod_cast T.skew j i

lemma block_representation {n : ℕ} (T : Tournament (Fin n)) (v z : ℂ) :
    blockMatrix T v z = 1 + z • blockQ T v := by
  ext i j
  cases i <;> cases j <;>
    simp [blockMatrix,blockQ,interaction,Matrix.fromBlocks,Matrix.one_apply,
      Matrix.transpose_add,Matrix.transpose_smul,sign_transpose,div_eq_mul_inv,
      smul_smul, mul_add, mul_assoc]

lemma schur_complement {n : ℕ} (T : Tournament (Fin n)) (v z : ℂ) (hv : v^2=1) :
    1 - ((z/(n:ℂ)) • (-signMatrix T + v • 1)) *
      ((z/(n:ℂ)) • (signMatrix T + v • 1)) = gaussianMatrix T z := by
  have hp : (-signMatrix T + v • (1 : Matrix (Fin n) (Fin n) ℂ)) *
      (signMatrix T + v • 1) = -(signMatrix T * signMatrix T) + (v*v) • 1 := by
    simp only [add_mul,mul_add,neg_mul,Matrix.mul_smul,Matrix.smul_mul,
      mul_one,one_mul,smul_smul]
    abel
  rw [Matrix.smul_mul,Matrix.mul_smul,smul_smul,hp]
  simp only [← pow_two,hv,one_smul,smul_add,smul_neg]
  unfold gaussianMatrix beta
  rw [sub_smul,one_smul]
  simp only [pow_two]
  abel

/-- The actual doubled block determinant equals the Gaussian denominator.
Only the two branches v²=1 are identified here. -/
theorem determinant {n : ℕ} (T : Tournament (Fin n)) (v z : ℂ) (hv : v^2=1) :
    (blockMatrix T v z).det = (gaussianMatrix T z).det := by
  unfold blockMatrix
  rw [Matrix.det_fromBlocks_one₁₁,schur_complement T v z hv]

theorem isUnit_block {n : ℕ} (T : Tournament (Fin n)) (v z : ℂ) (hv : v^2=1)
    (hb : beta n z ≠ 0) (hA : IsUnit (resolventMatrix T (parameter n z))) :
    IsUnit (blockMatrix T v z) := by
  rw [Matrix.isUnit_iff_isUnit_det,determinant T v z hv,matrix_scaled T z hb,
    Matrix.det_smul]
  exact (isUnit_iff_ne_zero.mpr (pow_ne_zero _ hb)).mul
    ((Matrix.isUnit_iff_isUnit_det _).mp hA)

theorem inverse_left_right {n : ℕ} (T : Tournament (Fin n)) (v z : ℂ) (hv : v^2=1)
    (hb : beta n z ≠ 0) (hA : IsUnit (resolventMatrix T (parameter n z))) :
    blockMatrix T v z * (blockMatrix T v z)⁻¹=1 ∧
    (blockMatrix T v z)⁻¹ * blockMatrix T v z=1 := by
  have hu := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_block T v z hv hb hA)
  exact ⟨Matrix.mul_nonsing_inv _ hu,Matrix.nonsing_inv_mul _ hu⟩
end BlockGaussianDeterminant
#print axioms BlockGaussianDeterminant.determinant
#print axioms BlockGaussianDeterminant.inverse_left_right
