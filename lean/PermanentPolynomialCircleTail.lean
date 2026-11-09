import Mathlib.Analysis.Polynomial.Fourier
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Analysis.SpecificLimits.Basic

/-! Verified circle-bound transfer. Circle-to-tail transfer for the actual
permanent polynomial. The circle bound is an explicit, still unproved input. -/
noncomputable section
open scoped BigOperators
open Complex MeasureTheory
namespace PermanentPolynomialCircleTail

/-- The finite polynomial is defined by the actual permanent over ℂ[X]. -/
def permanentPolynomial {n : ℕ} (P M : Matrix (Fin n) (Fin n) ℂ) : Polynomial ℂ :=
  Matrix.permanent (fun i j => Polynomial.C (P i j) + Polynomial.X * Polynomial.C (M i j))

lemma permanentPolynomial_eval {n : ℕ} (P M : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    (permanentPolynomial P M).eval z = Matrix.permanent (P + z • M) := by
  simp [permanentPolynomial, Matrix.permanent, Polynomial.eval_finsetSum,
    Polynomial.eval_prod, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro sigma hs
  apply Finset.prod_congr rfl
  intro i hi
  ring

theorem polynomial_circle_coefficient_bound (p : Polynomial ℂ) (R A : ℝ)
    (hR : 0 < R) (hA : 0 ≤ A)
    (hcircle : ∀ z : ℂ, ‖z‖ = R → ‖p.eval z‖ ≤ A) (k : ℕ) :
    ‖p.coeff k‖ ≤ A / R ^ k := by
  let q := p.comp (Polynomial.C (R : ℂ) * Polynomial.X)
  have hcont : Continuous (fun z : ℂ => ‖q.eval z‖ ^ 2) := by fun_prop
  have havg : Real.circleAverage (fun z : ℂ => ‖q.eval z‖ ^ 2) 0 1 ≤ A ^ 2 :=
    Real.circleAverage_mono_on_of_le_circle hcont.continuousOn.circleIntegrable' (by
      intro z hz
      have hz1 : ‖z‖ = 1 := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
      have hq : q.eval z = p.eval ((R : ℂ) * z) := by simp [q, Polynomial.eval_comp]
      have hn : ‖(R : ℂ) * z‖ = R := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, hz1, mul_one]
      rw [hq]
      exact pow_le_pow_left₀ (norm_nonneg _) (hcircle _ hn) 2)
  have hs : ‖q.coeff k‖ ^ 2 ≤ ∑ i ∈ q.support, ‖q.coeff i‖ ^ 2 := by
    by_cases hk : k ∈ q.support
    · exact Finset.single_le_sum (fun i _ => sq_nonneg ‖q.coeff i‖) hk
    · simp only [Polynomial.mem_support_iff, not_not] at hk
      rw [hk, norm_zero, zero_pow (by decide : 2 ≠ 0)]
      exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  rw [Polynomial.sum_sq_norm_coeff_eq_circleAverage] at hs
  have hcoef : ‖q.coeff k‖ = ‖p.coeff k‖ * R ^ k := by
    simp only [q, Polynomial.comp_C_mul_X_coeff, norm_mul, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  have hnorm : ‖q.coeff k‖ ≤ A := (sq_le_sq₀ (norm_nonneg _) hA).mp (hs.trans havg)
  rw [hcoef] at hnorm
  exact (le_div_iff₀ (pow_pos hR k)).mpr hnorm

theorem polynomial_circle_finite_tail_bound (p : Polynomial ℂ) (R A : ℝ)
    (hR : 1 < R) (hA : 0 ≤ A)
    (hcircle : ∀ z : ℂ, ‖z‖ = R → ‖p.eval z‖ ≤ A)
    (M N : ℕ) (hMN : M ≤ N) :
    (∑ k ∈ Finset.Ico M N, ‖p.coeff k‖) ≤ R / (R - 1) * A / R ^ M := by
  have hRp : 0 < R := by linarith
  have hr : R⁻¹ < 1 := by apply (inv_lt_one₀ hRp).mpr; exact hR
  have hg : (∑ k ∈ Finset.Ico M N, (R⁻¹) ^ k) ≤ (R⁻¹) ^ M / (1 - R⁻¹) := by
    rw [geom_sum_Ico' (ne_of_lt hr) hMN]
    exact div_le_div_of_nonneg_right (by linarith [pow_nonneg (inv_nonneg.mpr hRp.le) N]) (by linarith)
  calc
    _ ≤ ∑ k ∈ Finset.Ico M N, A / R ^ k :=
      Finset.sum_le_sum (fun k _ => polynomial_circle_coefficient_bound p R A hRp hA hcircle k)
    _ = A * ∑ k ∈ Finset.Ico M N, (R⁻¹) ^ k := by simp only [Finset.mul_sum, div_eq_mul_inv, inv_pow]
    _ ≤ A * ((R⁻¹) ^ M / (1 - R⁻¹)) := mul_le_mul_of_nonneg_left hg hA
    _ = _ := by
      rw [inv_pow]
      field_simp

/-- The entire actual polynomial tail outside a finite coefficient window. -/
theorem polynomial_circle_tail_bound (p : Polynomial ℂ) (R A : ℝ)
    (hR : 1 < R) (hA : 0 ≤ A)
    (hcircle : ∀ z : ℂ, ‖z‖ = R → ‖p.eval z‖ ≤ A) (M : ℕ) :
    (∑ k ∈ p.support.filter (fun k => M < k), ‖p.coeff k‖) ≤ R / (R - 1) * A / R ^ M := by
  let N := max M (p.natDegree + 1)
  have hsub : p.support.filter (fun k => M < k) ⊆ Finset.Ico M N := by
    intro k hk
    obtain ⟨hk, hm⟩ := Finset.mem_filter.mp hk
    apply Finset.mem_Ico.mpr
    have hd := Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hk)
    exact ⟨hm.le, lt_of_lt_of_le (by omega : k < p.natDegree + 1) (le_max_right _ _)⟩
  apply (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => norm_nonneg _)).trans
  exact polynomial_circle_finite_tail_bound p R A hR hA hcircle M N (le_max_left _ _)


/-- This is a circle-bound transfer, not a proof of the needed spectral
permanent circle envelope. No core/proxy coefficients occur in the statement. -/
theorem actual_permanent_tail {n : ℕ} (P M : Matrix (Fin n) (Fin n) ℂ)
    (R A : ℝ) (hR : 1 < R) (hA : 0 ≤ A)
    (hcircle : ∀ z : ℂ, ‖z‖ = R → ‖Matrix.permanent (P + z • M)‖ ≤ A)
    (m : ℕ) :
    (∑ k ∈ (permanentPolynomial P M).support.filter (fun k => m < k),
      ‖(permanentPolynomial P M).coeff k‖) ≤ R/(R-1)*A/R^m := by
  apply polynomial_circle_tail_bound _ R A hR hA _ m
  intro z hz
  rw [permanentPolynomial_eval]
  exact hcircle z hz

/-- Weighted coefficients are reduced to the unit-radius tail by scaling the
actual perturbation M, rather than introducing a formal Gaussian proxy. -/
theorem actual_permanent_scaled_tail {n : ℕ} (P M : Matrix (Fin n) (Fin n) ℂ)
    (rho R A : ℝ) (hR : 1 < R) (hA : 0 ≤ A)
    (hcircle : ∀ z : ℂ, ‖z‖ = R →
      ‖Matrix.permanent (P + z • ((rho : ℂ) • M))‖ ≤ A) (m : ℕ) :
    (∑ k ∈ (permanentPolynomial P ((rho : ℂ) • M)).support.filter (fun k => m < k),
      ‖(permanentPolynomial P ((rho : ℂ) • M)).coeff k‖) ≤ R/(R-1)*A/R^m :=
  actual_permanent_tail P ((rho : ℂ) • M) R A hR hA hcircle m

end PermanentPolynomialCircleTail
#print axioms PermanentPolynomialCircleTail.actual_permanent_tail
