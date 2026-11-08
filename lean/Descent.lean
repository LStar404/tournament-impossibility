import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push

/-! Rational descent for finite polynomial relations among power series.

The proof applies a Q-linear functional C → Q to the complex coefficients.
The functional is chosen nonzero on one nonzero relation coefficient.
No analytic hypothesis or transcendence result is assumed here.
-/

namespace NonAlgebraicity
open scoped BigOperators

/-- A finite system of rational linear equations with a nonzero complex
solution has a nonzero rational solution, even with infinitely many rows. -/
theorem finite_relation_descends {ι κ : Type*} [Fintype ι]
    (v : ι → κ → ℚ) (c : ι → ℂ) (hc : c ≠ 0)
    (hrel : ∀ k, ∑ i, (v i k : ℂ) * c i = 0) :
    ∃ d : ι → ℚ, d ≠ 0 ∧ ∀ k, ∑ i, v i k * d i = 0 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
    by_contra h
    push Not at h
    exact hc (funext h)
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero ℚ hi
  refine ⟨fun i => f (c i), ?_, ?_⟩
  · intro h
    exact hf (congrFun h i)
  · intro k
    have h := congrArg f (hrel k)
    simpa only [map_sum, map_zero, ← Rat.smul_def, map_smul, smul_eq_mul] using h

/-- Applying the preceding lemma to every power-series coefficient. -/
theorem powerSeries_relation_descends {ι : Type*} [Fintype ι]
    (v : ι → PowerSeries ℚ) (c : ι → ℂ) (hc : c ≠ 0)
    (hrel : ∑ i, c i • PowerSeries.map (algebraMap ℚ ℂ) (v i) = 0) :
    ∃ d : ι → ℚ, d ≠ 0 ∧ ∑ i, d i • v i = 0 := by
  classical
  have hcoeff : ∀ k, ∑ i, ((PowerSeries.coeff k (v i) : ℚ) : ℂ) * c i = 0 := by
    intro k
    have h := congrArg (PowerSeries.coeff k) hrel
    simpa [mul_comm] using h
  obtain ⟨d, hd, hde⟩ := finite_relation_descends
    (fun i k => PowerSeries.coeff k (v i)) c hc hcoeff
  refine ⟨d, hd, ?_⟩
  ext k
  simpa only [map_sum, PowerSeries.coeff_smul, map_zero, smul_eq_mul, mul_comm] using hde k

/-- A nonzero bivariate polynomial relation, encoded by a rectangular
coefficient array. Distinct index pairs are distinct monomials X^i Y^j.
This is the cleared-denominator meaning of algebraicity over K(z). -/
def HasPolynomialRelation {K : Type*} [Field K] (B : PowerSeries K) : Prop :=
  ∃ (m n : ℕ) (c : Fin m × Fin n → K), c ≠ 0 ∧
    ∑ ij, c ij • ((PowerSeries.X : PowerSeries K) ^ ij.1.val * B ^ ij.2.val) = 0

/-- Appendix A.2: allowing arbitrary complex polynomial coefficients
does not create a relation for a rational-coefficient formal power series. -/
theorem rational_polynomial_relation_descends (B : PowerSeries ℚ)
    (h : HasPolynomialRelation (PowerSeries.map (algebraMap ℚ ℂ) B)) :
    HasPolynomialRelation B := by
  classical
  obtain ⟨m, n, c, hc, hrel⟩ := h
  refine ⟨m, n, ?_⟩
  apply powerSeries_relation_descends
    (fun ij : Fin m × Fin n => (PowerSeries.X : PowerSeries ℚ) ^ ij.1.val * B ^ ij.2.val)
    c hc
  simpa using hrel

end NonAlgebraicity

#print axioms NonAlgebraicity.rational_polynomial_relation_descends
