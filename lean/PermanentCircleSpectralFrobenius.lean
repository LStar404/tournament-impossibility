import PermanentCircleSpectralCoordinates
noncomputable section
namespace PermanentSpectralFrame
open Matrix
open scoped ComplexOrder
variable {n : ℕ}

/-- The actual, unordered Gram spectrum has exactly the Frobenius square sum. -/
theorem singular_square_sum (A : Matrix (Fin n) (Fin n) ℂ) :
    (∑i, (singularRoot A i)^2) = ∑i,∑j, ‖A i j‖^2 := by
  simp_rw [singularRoot_sq]
  have h := (gram_positive A).isHermitian.trace_eq_sum_eigenvalues
  have hc : (gram A).trace = ((∑i,∑j, ‖A i j‖^2:ℝ):ℂ) := by
    simp only [gram, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.star_def, Complex.conj_mul', Complex.ofReal_sum, Complex.ofReal_pow]
    rw [Finset.sum_comm]
  change (gram A).trace = ∑i,(eigenvalue A i:ℂ) at h
  rw [hc, ← Complex.ofReal_sum] at h
  exact_mod_cast h.symm
end PermanentSpectralFrame
#print axioms PermanentSpectralFrame.singular_square_sum
