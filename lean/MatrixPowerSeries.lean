import StandardAlgebraicity
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Generating series of finite-dimensional matrix orbits

For a complex matrix `M`, the column of orbit generating series satisfies
`(I - X M) B = v`. Multiplication by the adjugate gives a polynomial
denominator with constant term one. Every linear output is therefore
algebraic over `ℂ[X]` (indeed rational), without any spectral assumptions.
-/

open scoped BigOperators
open Matrix Polynomial
namespace NonAlgebraicity

noncomputable def matrixOrbitSeries {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℂ) (v : Fin d → ℂ) (i : Fin d) : PowerSeries ℂ :=
  PowerSeries.mk fun n => ((M ^ n) *ᵥ v) i

noncomputable def matrixResolventPolynomial {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ[X] :=
  1 - (Polynomial.X : ℂ[X]) • M.map (Polynomial.C : ℂ →+* ℂ[X])

theorem matrixOrbitSeries_equation {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℂ) (v : Fin d → ℂ) :
    (matrixResolventPolynomial M).map (algebraMap ℂ[X] (PowerSeries ℂ)) *ᵥ
      matrixOrbitSeries M v = fun i => PowerSeries.C (v i) := by
  classical
  ext i n
  cases n with
  | zero => simp [matrixResolventPolynomial, matrixOrbitSeries, Matrix.mulVec, dotProduct,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply, apply_ite, ite_mul, PowerSeries.algebraMap_apply']
  | succ n =>
    have hp : ((M ^ (n + 1)) *ᵥ v) i = ∑ j, M i j * ((M ^ n) *ᵥ v) j := by
      rw [pow_succ', ← Matrix.mulVec_mulVec]
      rfl
    simpa [matrixResolventPolynomial, matrixOrbitSeries, Matrix.mulVec, dotProduct,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply, sub_mul,
      Finset.sum_sub_distrib, mul_assoc, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_C_mul, Matrix.one_apply, apply_ite, ite_mul, PowerSeries.algebraMap_apply'] using sub_eq_zero.mpr hp

theorem matrixResolventPolynomial_det_ne_zero {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℂ) : (matrixResolventPolynomial M).det ≠ 0 := by
  classical
  intro h
  have h0 := congrArg (Polynomial.evalRingHom (0 : ℂ)) h
  rw [RingHom.map_det] at h0
  have he : (matrixResolventPolynomial M).map (Polynomial.evalRingHom (0 : ℂ)) = 1 := by
    ext i j
    simp [matrixResolventPolynomial, Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply, apply_ite]
  have he' : (Polynomial.evalRingHom (0 : ℂ)).mapMatrix (matrixResolventPolynomial M) = 1 := he
  rw [he', Matrix.det_one, map_zero] at h0
  exact one_ne_zero h0

/-- A scalar output of powers of a finite complex matrix has an algebraic
formal generating series over the polynomial ring.
The adjugate identity supplies an explicit nonzero polynomial relation. -/
theorem matrix_output_series_linear_relation {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℂ) (v l : Fin d → ℂ) :
    ∃ P Q : ℂ[X], Q ≠ 0 ∧
      (algebraMap ℂ[X] (PowerSeries ℂ)) Q *
        (PowerSeries.mk fun n => l ⬝ᵥ ((M ^ n) *ᵥ v)) =
      (algebraMap ℂ[X] (PowerSeries ℂ)) P := by
  classical
  let f : ℂ[X] →+* PowerSeries ℂ := algebraMap ℂ[X] (PowerSeries ℂ)
  let A := matrixResolventPolynomial M
  let B := matrixOrbitSeries M v
  let Q := A.det
  let P := (fun i => Polynomial.C (l i)) ⬝ᵥ (A.adjugate *ᵥ (fun i => Polynomial.C (v i)))
  have hQ : Q ≠ 0 := matrixResolventPolynomial_det_ne_zero M
  have heq : A.map f *ᵥ B = fun i => PowerSeries.C (v i) := matrixOrbitSeries_equation M v
  have hcoord (i : Fin d) : f Q * B i = f ((A.adjugate *ᵥ (fun i => Polynomial.C (v i))) i) := by
    have hh := congrArg (fun w => ((A.map f).adjugate *ᵥ w) i) heq
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul] at hh
    have ha : (A.map f).adjugate = A.adjugate.map f := (f.map_adjugate A).symm
    rw [ha] at hh
    simpa [Q, RingHom.map_det, RingHom.map_mulVec, Function.comp_def,
      f, PowerSeries.algebraMap_apply', Matrix.smul_mulVec, Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul] using hh
  have hseries : (PowerSeries.mk fun n => l ⬝ᵥ ((M ^ n) *ᵥ v)) =
      ∑ i, PowerSeries.C (l i) * B i := by
    ext n
    simp [B, matrixOrbitSeries, dotProduct, PowerSeries.coeff_C_mul]
  have hrel : f Q * (PowerSeries.mk fun n => l ⬝ᵥ ((M ^ n) *ᵥ v)) = f P := by
    rw [hseries, Finset.mul_sum]
    simp only [P, dotProduct, map_sum, map_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [← mul_assoc, mul_comm (f Q), mul_assoc, hcoord]
    simp [f, PowerSeries.algebraMap_apply']
  exact ⟨P, Q, hQ, hrel⟩

theorem matrix_output_series_isAlgebraic {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℂ) (v l : Fin d → ℂ) :
    IsAlgebraic ℂ[X] (PowerSeries.mk fun n => l ⬝ᵥ ((M ^ n) *ᵥ v)) := by
  obtain ⟨P, Q, hQ, hrel⟩ := matrix_output_series_linear_relation M v l
  let f : ℂ[X] →+* PowerSeries ℂ := algebraMap ℂ[X] (PowerSeries ℂ)
  refine ⟨Polynomial.C Q * Polynomial.X - Polynomial.C P, ?_, ?_⟩
  · intro hz
    have hh := congrArg (Polynomial.coeff · 1) hz
    exact hQ (by simpa using hh)
  · simpa [Polynomial.aeval_def, f, sub_eq_zero] using hrel

/-- Finite coefficient-array form, suitable for rational-coefficient descent. -/
theorem matrix_output_series_relation {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℂ) (v l : Fin d → ℂ) :
    HasPolynomialRelation (PowerSeries.mk fun n => l ⬝ᵥ ((M ^ n) *ᵥ v)) :=
  hasPolynomialRelation_of_isAlgebraic _ (matrix_output_series_isAlgebraic M v l)

end NonAlgebraicity

#print axioms NonAlgebraicity.matrix_output_series_relation
