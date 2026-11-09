import GaussianScalarFactor
import DiamondFreeComplexResolvent

noncomputable section
namespace GaussianDeterminantBranch
open Matrix DiamondGap DiamondFreeKernelDeterminant DiamondFreeComplexResolvent
open GaussianParameterBranch GaussianScalarFactor DiamondFreeKernelLimit

def gaussianMatrix {n : ℕ} (T : Tournament (Fin n)) (z : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  beta n z • 1 + (z/(n:ℂ))^2 • (signMatrix T * signMatrix T)

lemma prefactor_eq_root_pow (n : ℕ) (z : ℂ) : prefactor n z=(root n z)^n := by
  rw [prefactor,root,← Complex.exp_nat_mul]
  congr 1
  ring

lemma prefactor_square (n : ℕ) (z : ℂ) (hb : beta n z≠0) :
    (prefactor n z)^2*(beta n z)^n=1 := by
  rw [prefactor_eq_root_pow]
  have h := congrArg (fun x : ℂ => x^n) (root_identity n z hb)
  simpa [mul_pow,← pow_mul,Nat.mul_comm] using h

lemma matrix_scaled {n : ℕ} (T : Tournament (Fin n)) (z : ℂ)
    (hb : beta n z≠0) : gaussianMatrix T z=beta n z • resolventMatrix T (parameter n z) := by
  have hr := root_identity n z hb
  unfold gaussianMatrix resolventMatrix
  rw [smul_add,smul_smul]
  congr 1
  have hc : (z/(n:ℂ))^2=beta n z*(parameter n z/(n:ℂ))^2 := by
    unfold parameter
    calc
      _ = (z/(n:ℂ))^2*((root n z)^2*beta n z) := by rw [hr,mul_one]
      _ = _ := by ring
  rw [hc]

lemma determinant_formula {n : ℕ} (T : Tournament (Fin n)) (hT : T.diamonds.card=0)
    (z : ℂ) (hb : beta n z≠0) :
    (gaussianMatrix T z).det=(beta n z)^n*(finiteKernel n (parameter n z*Complex.I))^2 := by
  rw [matrix_scaled T z hb,Matrix.det_smul,factorization,Matrix.det_mul,
    zero_diamonds_kernel_det T hT,zero_diamonds_kernel_det T hT]
  simp [finiteKernel,Fintype.card_fin,sub_eq_add_neg,add_comm,pow_two]

/-- The chosen scalar Gaussian factor is an actual inverse-square-root branch
of the graph determinant, not an unrelated function with the same limit. -/
theorem gaussian_branch_square {n : ℕ} (T : Tournament (Fin n)) (hT : T.diamonds.card=0)
    (z : ℂ) (hb : beta n z≠0) (hH : finiteKernel n (parameter n z*Complex.I)≠0) :
    (gaussian n z)^2*(gaussianMatrix T z).det=1 := by
  rw [gaussian,determinant_formula T hT z hb]
  calc
    _ = (prefactor n z)^2*(beta n z)^n := by field_simp [hH]
    _ = 1 := prefactor_square n z hb
end GaussianDeterminantBranch
#print axioms GaussianDeterminantBranch.gaussian_branch_square
