import PermanentFactorEnergy
import Mathlib.Analysis.CStarAlgebra.Matrix
noncomputable section
namespace PermanentSpectralFrame
open Matrix
variable {n : ℕ}

/-- Actual Gram-frame coordinates, without an ordered-spectrum assumption. -/
theorem frame_energy (A : Matrix (Fin n) (Fin n) ℂ) (c : Fin n → ℂ) :
    (∑i, ‖((frame A:Matrix (Fin n) (Fin n) ℂ)*ᵥc) i‖^2) = ∑i, ‖c i‖^2 := by
  have h := gram_energy (frame A) (fun _ => (1:ℝ)) (by simpa using frame_star_mul A) c
  simpa using h

theorem image_frame_energy (A : Matrix (Fin n) (Fin n) ℂ) (c : Fin n → ℂ) :
    (∑i, ‖(A*ᵥ((frame A:Matrix (Fin n) (Fin n) ℂ)*ᵥc)) i‖^2) =
      ∑i, eigenvalue A i * ‖c i‖^2 := by
  have hg : (A*(frame A:Matrix (Fin n) (Fin n) ℂ))ᴴ*(A*(frame A:Matrix (Fin n) (Fin n) ℂ))=diagonal (fun i => (eigenvalue A i:ℂ)) := by
    rw [conjTranspose_mul]
    simpa only [Matrix.mul_assoc] using frame_gram A
  simpa only [mulVec_mulVec] using gram_energy (A*(frame A:Matrix (Fin n) (Fin n) ℂ)) (eigenvalue A) hg c

/-- An actual Euclidean operator bound yields the squared coordinate inequality. -/
theorem matrix_operator_energy (E : Matrix (Fin n) (Fin n) ℂ) (q : ℝ)
    (hq : 0≤q) (hE : ‖Matrix.toEuclideanCLM (𝕜:=ℂ) E‖ ≤ q) (x : Fin n → ℂ) :
    (∑i, ‖(E*ᵥx) i‖^2) ≤ q^2 * ∑i, ‖x i‖^2 := by
  let v : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 x
  have h := (Matrix.toEuclideanCLM (𝕜:=ℂ) E).le_opNorm v
  have hh := h.trans (mul_le_mul_of_nonneg_right hE (norm_nonneg v))
  have hp := pow_le_pow_left₀ (norm_nonneg _) hh 2
  have hv : Matrix.toEuclideanCLM (𝕜:=ℂ) E v =
      WithLp.toLp 2 (E *ᵥ x) := by
    apply WithLp.ofLp_injective
    rw [Matrix.ofLp_toEuclideanCLM]
  rw [hv] at hp
  simpa [v, EuclideanSpace.norm_sq_eq, mul_pow] using hp
end PermanentSpectralFrame
#print axioms PermanentSpectralFrame.image_frame_energy
