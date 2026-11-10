import RawCoordinateTaylor
import BlockGaussianSourceElimination
import RawBlockSourceIdentity

/-!
Independent finite-algebra extension; not part of the frozen 372 source tree.

This is finite matrix algebra for the actual inverse. The two scalar parameters
are independent: `f` scales S and `b` scales I. No division by f or b is used.
For the existing raw branch, substitute f = a and b = a*v.
-/
noncomputable section
namespace RawFourBlockResolvent
open Matrix
variable {I : Type*} [Fintype I] [DecidableEq I]

def upper (S : Matrix I I ℂ) (f b : ℂ) : Matrix I I ℂ := f • S + b • 1
def lower (S : Matrix I I ℂ) (f b : ℂ) : Matrix I I ℂ := -(f • S) + b • 1
def system (S : Matrix I I ℂ) (f b : ℂ) : Matrix (I ⊕ I) (I ⊕ I) ℂ :=
  fromBlocks 1 (upper S f b) (lower S f b) 1
def schur (S : Matrix I I ℂ) (f b : ℂ) : Matrix I I ℂ :=
  (1-b^2) • 1 + f^2 • (S*S)
def resolvent (S : Matrix I I ℂ) (f b : ℂ) : Matrix I I ℂ := (schur S f b)⁻¹
def kernel (S : Matrix I I ℂ) (f b : ℂ) : Matrix (I ⊕ I) (I ⊕ I) ℂ :=
  (system S f b-1)*(system S f b)⁻¹

omit [Fintype I] in
lemma lower_eq_transpose (S : Matrix I I ℂ) (f b : ℂ) (hS : S.transpose=-S) :
    lower S f b=(upper S f b).transpose := by
  simp only [upper,lower,Matrix.transpose_add,Matrix.transpose_smul,
    Matrix.transpose_one,hS,smul_neg]

lemma upper_mul_lower (S : Matrix I I ℂ) (f b : ℂ) :
    upper S f b * lower S f b = -(f^2) • (S*S) + b^2 • 1 := by
  simp only [upper,lower,add_mul,mul_add,mul_neg,
    Matrix.smul_mul,Matrix.mul_smul,smul_smul,mul_one,one_mul]
  module

lemma lower_mul_upper (S : Matrix I I ℂ) (f b : ℂ) :
    lower S f b * upper S f b = -(f^2) • (S*S) + b^2 • 1 := by
  simp only [upper,lower,add_mul,mul_add,neg_mul,
    Matrix.smul_mul,Matrix.mul_smul,smul_smul,mul_one,one_mul]
  module

lemma offDiagonal_commute (S : Matrix I I ℂ) (f b : ℂ) :
    upper S f b * lower S f b = lower S f b * upper S f b := by
  rw [upper_mul_lower,lower_mul_upper]

lemma schur_eq (S : Matrix I I ℂ) (f b : ℂ) :
    1-lower S f b*upper S f b = schur S f b := by
  rw [lower_mul_upper]
  unfold schur
  module

/-- A genuine right inverse; commutation is needed only for the two diagonal
blocks. In particular no assertion about the inverse commuting is assumed. -/
theorem block_right_inverse (A B K : Matrix I I ℂ)
    (hAB : A*B=B*A) (hK : (1-B*A)*K=1) :
    fromBlocks (1 : Matrix I I ℂ) A B 1 *
      fromBlocks K (-(A*K)) (-(B*K)) K = 1 := by
  have h11 : (1 : Matrix I I ℂ)*K+A*(-(B*K))=1 := by
    calc
      _ = (1-A*B)*K := by noncomm_ring
      _ = (1-B*A)*K := by rw [hAB]
      _ = 1 := hK
  have h12 : (1 : Matrix I I ℂ)*(-(A*K))+A*K=0 := by simp
  have h21 : B*K+(1 : Matrix I I ℂ)*(-(B*K))=0 := by simp
  have h22 : B*(-(A*K))+(1 : Matrix I I ℂ)*K=1 := by
    calc
      _ = (1-B*A)*K := by noncomm_ring
      _ = 1 := hK
  rw [Matrix.fromBlocks_multiply,h11,h12,h21,h22,Matrix.fromBlocks_one]

theorem right_inverse (S : Matrix I I ℂ) (f b : ℂ)
    (hD : IsUnit (schur S f b)) :
    system S f b * fromBlocks (resolvent S f b)
      (-(upper S f b*resolvent S f b))
      (-(lower S f b*resolvent S f b)) (resolvent S f b) = 1 := by
  apply block_right_inverse _ _ _ (offDiagonal_commute S f b)
  rw [schur_eq]
  exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hD)

theorem isUnit_system (S : Matrix I I ℂ) (f b : ℂ)
    (hD : IsUnit (schur S f b)) : IsUnit (system S f b) := by
  exact isUnit_iff_exists_inv.mpr ⟨_,right_inverse S f b hD⟩

/-- All four blocks of the actual nonsingular inverse, not a formal proxy. -/
theorem inverse_four_blocks (S : Matrix I I ℂ) (f b : ℂ)
    (hD : IsUnit (schur S f b)) :
    (system S f b)⁻¹ = fromBlocks (resolvent S f b)
      (-(upper S f b*resolvent S f b))
      (-(lower S f b*resolvent S f b)) (resolvent S f b) :=
  Matrix.inv_eq_right_inv (right_inverse S f b hD)

lemma difference_times_inverse (A : Matrix I I ℂ) (hA : IsUnit A) :
    (A-1)*A⁻¹=1-A⁻¹ := by
  rw [sub_mul,Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hA),one_mul]

theorem kernel_four_blocks (S : Matrix I I ℂ) (f b : ℂ)
    (hD : IsUnit (schur S f b)) :
    kernel S f b = fromBlocks (1-resolvent S f b)
      (upper S f b*resolvent S f b)
      (lower S f b*resolvent S f b) (1-resolvent S f b) := by
  unfold kernel
  rw [difference_times_inverse _ (isUnit_system S f b hD),inverse_four_blocks S f b hD]
  ext i j
  cases i <;> cases j <;> simp [Matrix.fromBlocks,Matrix.one_apply]

theorem mean_four_blocks (S : Matrix I I ℂ) (f b : ℂ)
    (hD : IsUnit (schur S f b)) :
    (kernel S f b).mulVec (fun _ => 1) =
      Sum.elim
        (((1-resolvent S f b).mulVec (fun _ => 1))+
          (upper S f b*resolvent S f b).mulVec (fun _ => 1))
        (((lower S f b*resolvent S f b).mulVec (fun _ => 1))+
          (1-resolvent S f b).mulVec (fun _ => 1)) := by
  rw [kernel_four_blocks S f b hD]
  exact Matrix.fromBlocks_mulVec _ _ _ _ (fun _ => 1)

omit [Fintype I] in
/-- Reuse the existing source-system definition; no new scalar source theorem
or Gaussian determinant normalization is asserted here. -/
theorem system_eq_existing (S : Matrix I I ℂ) (a v : ℂ) :
    system S a (a*v)=BlockGaussianSourceElimination.blockSystem S a v := by
  simp only [system,upper,lower,BlockGaussianSourceElimination.blockSystem,
    smul_add,smul_neg,smul_smul]

def interaction (S : Matrix I I ℂ) (v : ℂ) : Matrix (I ⊕ I) (I ⊕ I) ℂ :=
  fromBlocks 0 (S+v • 1) (-S+v • 1) 0

omit [Fintype I] in
theorem actual_eq_system (S : Matrix I I ℂ) (a v : ℂ) :
    AffineMatrixTaylorBridge.actual (interaction S v) a=system S a (a*v) := by
  rw [system_eq_existing]
  unfold AffineMatrixTaylorBridge.actual interaction BlockGaussianSourceElimination.blockSystem
  rw [Matrix.fromBlocks_smul,← Matrix.fromBlocks_one,Matrix.fromBlocks_add]
  simp

/-- This is exactly the covariance already linked to PhysicalTiltedCovariance
by RawCoordinateTaylor.covariance_series. -/
theorem raw_covariance_eq_kernel (S : Matrix I I ℂ) (a v : ℂ) :
    RawCoordinateTaylor.covariance (interaction S v) a=kernel S a (a*v) := by
  have hdiff : a • interaction S v=system S a (a*v)-1 := by
    rw [← actual_eq_system]
    simp only [AffineMatrixTaylorBridge.actual,add_sub_cancel_left]
  unfold RawCoordinateTaylor.covariance kernel
  -- The existing covariance fixes classical equality on its whole index type.
  have hdec : Classical.typeDecidableEq (I ⊕ I) =
      (inferInstance : DecidableEq (I ⊕ I)) := Subsingleton.elim _ _
  rw [hdec,actual_eq_system,hdiff]

theorem raw_covariance_four_blocks (S : Matrix I I ℂ) (a v : ℂ)
    (hD : IsUnit (schur S a (a*v))) :
    RawCoordinateTaylor.covariance (interaction S v) a =
      fromBlocks (1-resolvent S a (a*v))
        (upper S a (a*v)*resolvent S a (a*v))
        (lower S a (a*v)*resolvent S a (a*v)) (1-resolvent S a (a*v)) := by
  rw [raw_covariance_eq_kernel]
  exact kernel_four_blocks S a (a*v) hD

/-- Explicitly reuse the previously proved reduction of the old raw source.
The current module contributes its invertibility input, not a redefinition. -/
theorem source_eq_existing_reduction {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ)
    (f b : ℂ) (hD : IsUnit (schur S f b)) :
    RawBlockSourceIdentity.rawSource (system S f b) =
      (n:ℂ)-((fun _ : Fin n => (1:ℂ)) ⬝ᵥ
        RawBlockSourceIdentity.sumSolution (system S f b))/2 := by
  apply RawBlockSourceIdentity.source_eq_reduced
  exact Matrix.mul_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp (isUnit_system S f b hD))

end RawFourBlockResolvent
#print axioms RawFourBlockResolvent.inverse_four_blocks
#print axioms RawFourBlockResolvent.kernel_four_blocks
#print axioms RawFourBlockResolvent.raw_covariance_four_blocks
#print axioms RawFourBlockResolvent.source_eq_existing_reduction
