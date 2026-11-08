import Descent
import Mathlib.Tactic

open Polynomial
open scoped BigOperators
namespace NonAlgebraicity

noncomputable def dualPolynomial (f : ℂ →ₗ[ℚ] ℚ) (P : ℂ[X]) : ℚ[X] :=
  ∑ i ∈ Finset.range (P.natDegree + 1), Polynomial.monomial i (f (P.coeff i))

@[simp] theorem coeff_dualPolynomial (f : ℂ →ₗ[ℚ] ℚ) (P : ℂ[X]) (n : ℕ) :
    (dualPolynomial f P).coeff n = f (P.coeff n) := by
  classical
  by_cases hn : n < P.natDegree + 1
  · simp [dualPolynomial, Polynomial.coeff_monomial, hn]
  · have hz : P.coeff n = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    simp [dualPolynomial, Polynomial.coeff_monomial, hn, hz]

/-- A rational formal series which is a quotient of complex polynomials is
already a quotient of rational polynomials. A rational-linear functional
preserving one denominator coefficient descends the entire identity. -/
theorem rational_linear_relation_descends (B : PowerSeries ℚ)
    (P Q : ℂ[X]) (hQ : Q ≠ 0)
    (hrel : algebraMap ℂ[X] (PowerSeries ℂ) Q *
      PowerSeries.map (algebraMap ℚ ℂ) B = algebraMap ℂ[X] (PowerSeries ℂ) P) :
    ∃ p q : ℚ[X], q ≠ 0 ∧
      algebraMap ℚ[X] (PowerSeries ℚ) q * B = algebraMap ℚ[X] (PowerSeries ℚ) p := by
  classical
  have hcoeff : Q.coeff Q.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero ℚ hcoeff
  refine ⟨dualPolynomial f P, dualPolynomial f Q, ?_, ?_⟩
  · intro hz
    have hh := congrArg (Polynomial.coeff · Q.natDegree) hz
    exact hf (by simpa using hh)
  · ext n
    have hh := congrArg (fun F : PowerSeries ℂ => f (PowerSeries.coeff n F)) hrel
    simp only [PowerSeries.coeff_mul, PowerSeries.coeff_map,
      PowerSeries.algebraMap_apply', Polynomial.coeff_coe,
      map_sum] at hh ⊢
    simp only [coeff_dualPolynomial]
    convert hh using 1
    · apply Finset.sum_congr rfl
      intro ij hij
      simpa [Rat.smul_def, Algebra.smul_def, mul_comm] using
        (f.map_smul (PowerSeries.coeff ij.2 B) (Q.coeff ij.1)).symm

end NonAlgebraicity
#print axioms NonAlgebraicity.rational_linear_relation_descends
