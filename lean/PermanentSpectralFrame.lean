import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-! Actual spectral data of Aᴴ*A, with no externally
assumed diagonalization or zero-eigenvalue kernel condition. -/
noncomputable section
namespace PermanentSpectralFrame
open Matrix Unitary
open scoped ComplexOrder
variable {n : ℕ}

def gram (A : Matrix (Fin n) (Fin n) ℂ) := Aᴴ * A

lemma gram_positive (A : Matrix (Fin n) (Fin n) ℂ) : (gram A).PosSemidef :=
  Matrix.posSemidef_conjTranspose_mul_self A

def frame (A : Matrix (Fin n) (Fin n) ℂ) : Matrix.unitaryGroup (Fin n) ℂ :=
  (gram_positive A).isHermitian.eigenvectorUnitary

def eigenvalue (A : Matrix (Fin n) (Fin n) ℂ) : Fin n → ℝ :=
  (gram_positive A).isHermitian.eigenvalues

def singularRoot (A : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) : ℝ :=
  Real.sqrt (eigenvalue A i)

def fourthRoot (A : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) : ℝ :=
  Real.sqrt (singularRoot A i)

def rightFactor (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (frame A : Matrix (Fin n) (Fin n) ℂ) * diagonal (fun i => (fourthRoot A i : ℂ))

def leftFactor (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  A * (frame A : Matrix (Fin n) (Fin n) ℂ) *
    diagonal (fun i => (fourthRoot A i : ℂ)⁻¹)

lemma eigenvalue_nonneg (A : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    0 ≤ eigenvalue A i := (gram_positive A).eigenvalues_nonneg i

lemma singularRoot_sq (A : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    (singularRoot A i)^2=eigenvalue A i :=
  Real.sq_sqrt (eigenvalue_nonneg A i)

lemma fourthRoot_sq (A : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    (fourthRoot A i)^2=singularRoot A i :=
  Real.sq_sqrt (Real.sqrt_nonneg _)

/-- The chosen frame genuinely diagonalizes the actual Gram matrix. -/
theorem spectral_representation (A : Matrix (Fin n) (Fin n) ℂ) :
    gram A = (frame A : Matrix (Fin n) (Fin n) ℂ) *
      diagonal (fun i => (eigenvalue A i : ℂ)) *
      (frame A : Matrix (Fin n) (Fin n) ℂ)ᴴ := by
  simpa [frame,eigenvalue,conjStarAlgAut_apply,Function.comp_def,
    Matrix.star_eq_conjTranspose] using (gram_positive A).isHermitian.spectral_theorem

/-- A zero eigenvalue annihilates the actual column under A. This handles
singular matrices without assuming invertibility or completing a left basis. -/
theorem zero_eigenvalue_column (A : Matrix (Fin n) (Fin n) ℂ) (i : Fin n)
    (hi : eigenvalue A i=0) :
    A.mulVec (fun j => (frame A : Matrix (Fin n) (Fin n) ℂ) j i)=0 := by
  apply (Matrix.conjTranspose_mul_self_mulVec_eq_zero A _).mp
  have h := (gram_positive A).isHermitian.mulVec_eigenvectorBasis i
  have hz : (gram A).mulVec (fun j => (frame A : Matrix (Fin n) (Fin n) ℂ) j i)=0 := by
    change (gram_positive A).isHermitian.eigenvalues i = 0 at hi
    simpa [frame,Matrix.IsHermitian.eigenvectorUnitary_apply,hi] using h
  exact hz

end PermanentSpectralFrame
#print axioms PermanentSpectralFrame.spectral_representation
#print axioms PermanentSpectralFrame.zero_eigenvalue_column
