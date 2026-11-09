import PermanentSpectralFactors
import Mathlib.Analysis.Complex.Basic
noncomputable section
namespace PermanentSpectralFrame
open Matrix
variable {n : ℕ}
lemma gram_energy (X : Matrix (Fin n) (Fin n) ℂ) (s : Fin n → ℝ)
    (hX : Xᴴ*X=diagonal (fun i => (s i:ℂ))) (g : Fin n → ℂ) :
    (∑i, ‖(X*ᵥg) i‖^2) = ∑i, s i * ‖g i‖^2 := by
  have hc : star (X*ᵥg) ⬝ᵥ (X*ᵥg) =
      star g ⬝ᵥ ((diagonal (fun i => (s i:ℂ)))*ᵥg) := by
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hX]
  have hl : star (X*ᵥg) ⬝ᵥ (X*ᵥg) = ((∑i, ‖(X*ᵥg) i‖^2 : ℝ):ℂ) := by
    simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul', Complex.ofReal_sum, Complex.ofReal_pow]
  have hr : star g ⬝ᵥ ((diagonal (fun i => (s i:ℂ)))*ᵥg) =
      ((∑i, s i * ‖g i‖^2 : ℝ):ℂ) := by
    simp only [dotProduct, mulVec_diagonal, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow]
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_left_comm, Complex.star_def, Complex.conj_mul']
  rw [hl,hr] at hc
  exact_mod_cast hc

theorem actual_factor_energy (A : Matrix (Fin n) (Fin n) ℂ) (g : Fin n → ℂ) :
    (∑i, ‖(leftFactor A*ᵥg) i‖^2) = ∑i, singularRoot A i * ‖g i‖^2 :=
  gram_energy _ _ (leftFactor_gram A) g

theorem actual_right_energy (A : Matrix (Fin n) (Fin n) ℂ) (g : Fin n → ℂ) :
    (∑i, ‖(rightFactor A*ᵥg) i‖^2) = ∑i, singularRoot A i * ‖g i‖^2 :=
  gram_energy _ _ (rightFactor_gram A) g
end PermanentSpectralFrame
#print axioms PermanentSpectralFrame.actual_factor_energy
