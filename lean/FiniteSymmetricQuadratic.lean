import ActualHessianFinite
import Mathlib.Analysis.Real.Sqrt

/-! Verified in the 557-module direct-Lean compilation and declaration audit. Finite estimates only; no infinity-to-L2 conversion. -/
noncomputable section
namespace FiniteSymmetricQuadratic
open Finset Matrix WithLp
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def energy (z : ι → ℝ) : ℝ := ∑ i, z i ^ 2
def l2 (z : ι → ℝ) : ℝ := Real.sqrt (energy z)
def quad (A : Matrix ι ι ℝ) (z : ι → ℝ) : ℝ := ∑ i, ∑ j, A i j * z i * z j
lemma energy_nonneg (z : ι → ℝ) : 0 ≤ energy z :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)
lemma norm_eq_l2 (z : ι → ℝ) : ‖(toLp 2 z : EuclideanSpace ℝ ι)‖ = l2 z := by
  unfold l2 energy
  rw [← EuclideanSpace.real_norm_sq_eq]
  exact (Real.sqrt_sq (norm_nonneg _)).symm
lemma quad_eq_dot (A : Matrix ι ι ℝ) (z : ι → ℝ) :
    quad A z = ∑ i, z i * (A *ᵥ z) i := by
  unfold quad Matrix.mulVec dotProduct
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _; ring

/-- Symmetry converts column sums back to the same row budget. -/
theorem symmetric_row_quadratic (A : Matrix ι ι ℝ) (z : ι → ℝ) (d : ℝ)
    (hs : ∀ i j, A j i = A i j) (hrow : ∀ i, ∑ j, |A i j| ≤ d) :
    |quad A z| ≤ d * energy z := by
  have hc : ∀ j, ∑ i, |A i j| ≤ d := by
    intro j; simpa only [hs] using hrow j
  have hr : (∑ i, ∑ j, |A i j| * z i ^ 2) ≤ d * energy z := by
    simp only [← Finset.sum_mul]
    calc
      _ ≤ ∑ i, d * z i ^ 2 := Finset.sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg _))
      _ = _ := by rw [← Finset.mul_sum]; rfl
  have ht : (∑ i, ∑ j, |A i j| * z j ^ 2) ≤ d * energy z := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul]
    calc
      _ ≤ ∑ j, d * z j ^ 2 := Finset.sum_le_sum (fun j _ =>
        mul_le_mul_of_nonneg_right (hc j) (sq_nonneg _))
      _ = _ := by rw [← Finset.mul_sum]; rfl
  have hp (i j : ι) : |A i j * z i * z j| ≤
      |A i j| * (z i ^ 2 + z j ^ 2) / 2 := by
    rw [abs_mul, abs_mul]
    have h : 2 * (|z i| * |z j|) ≤ z i ^ 2 + z j ^ 2 := by
      nlinarith [sq_nonneg (|z i| - |z j|), sq_abs (z i), sq_abs (z j)]
    nlinarith [mul_le_mul_of_nonneg_left h (abs_nonneg (A i j))]
  calc
    _ ≤ ∑ i, |∑ j, A i j * z i * z j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |A i j * z i * z j| := Finset.sum_le_sum (fun i _ =>
      Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, |A i j| * (z i ^ 2 + z j ^ 2) / 2 :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hp i j))
    _ = ((∑ i, ∑ j, |A i j| * z i ^ 2) +
        (∑ i, ∑ j, |A i j| * z j ^ 2)) / 2 := by
      simp [mul_add, Finset.sum_add_distrib, ← Finset.sum_div]
    _ ≤ d * energy z := by linarith

/-- Actual Euclidean operator bound, not a coordinatewise inverse bound. -/
theorem spectral_quadratic_lower (Q : Matrix ι ι ℝ) (z : ι → ℝ)
    {q : ℝ} (hq : 0 ≤ q) (hQ : ‖Matrix.toEuclideanCLM (𝕜:=ℝ) Q‖ ≤ q) :
    -(q * energy z) ≤ quad Q z := by
  have hv : l2 (Q *ᵥ z) ≤ q * l2 z := by
    have h := (Matrix.toEuclideanCLM (𝕜:=ℝ) Q).le_opNorm (toLp 2 z)
    have hh := h.trans (mul_le_mul_of_nonneg_right hQ (norm_nonneg _))
    change ‖(toLp 2 (Q *ᵥ z) : EuclideanSpace ℝ ι)‖ ≤ q * ‖(toLp 2 z : EuclideanSpace ℝ ι)‖ at hh
    simpa only [norm_eq_l2] using hh
  have hs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset ι)
    (fun i => -z i) (fun i => (Q *ᵥ z) i)
  have hc : -quad Q z ≤ l2 z * l2 (Q *ᵥ z) := by
    simpa [quad_eq_dot, l2, energy, neg_mul, Finset.sum_neg_distrib] using hs
  have hz : 0 ≤ l2 z := Real.sqrt_nonneg _
  have hz2 : l2 z ^ 2 = energy z := Real.sq_sqrt (energy_nonneg z)
  have hm := mul_le_mul_of_nonneg_left hv hz
  nlinarith
end FiniteSymmetricQuadratic
#print axioms FiniteSymmetricQuadratic.symmetric_row_quadratic
#print axioms FiniteSymmetricQuadratic.spectral_quadratic_lower
