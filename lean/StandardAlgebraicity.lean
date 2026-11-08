import Descent
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Algebra.Polynomial.Eval.Degree

namespace NonAlgebraicity
open scoped BigOperators
open Polynomial

theorem polynomial_toSeries_fin {K : Type*} [Field K] (p : K[X]) {n : ℕ}
    (hn : p.natDegree < n) :
    algebraMap K[X] (PowerSeries K) p =
      ∑ i : Fin n, p.coeff i.val • (PowerSeries.X : PowerSeries K) ^ i.val := by
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow' hn]
  rw [map_sum, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  simp [PowerSeries.algebraMap_apply', Algebra.smul_def]

/-- Bridge from Mathlib's standard algebraicity predicate over K[X]
to the finite coefficient-array relation used in the descent proof. -/
theorem hasPolynomialRelation_of_isAlgebraic {K : Type*} [Field K]
    (B : PowerSeries K) (h : IsAlgebraic K[X] B) : HasPolynomialRelation B := by
  classical
  obtain ⟨p, hp, he⟩ := h
  let m := p.natDegree + 1
  let n := p.support.sup (fun j => (p.coeff j).natDegree) + 1
  have hn (j : ℕ) : (p.coeff j).natDegree < n := by
    by_cases hj : j ∈ p.support
    · exact Nat.lt_succ_of_le (Finset.le_sup (f := fun j => (p.coeff j).natDegree) hj)
    · have hj0 : p.coeff j = 0 := by simpa using hj
      simp only [hj0, Polynomial.natDegree_zero]
      exact Nat.zero_lt_succ _
  let c : Fin n × Fin m → K := fun ij => (p.coeff ij.2.val).coeff ij.1.val
  refine ⟨n, m, c, ?_, ?_⟩
  · intro hc
    obtain ⟨j, hj⟩ : ∃ j, p.coeff j ≠ 0 := by
      by_contra h
      push Not at h
      exact hp (Polynomial.ext h)
    obtain ⟨i, hi⟩ : ∃ i, (p.coeff j).coeff i ≠ 0 := by
      by_contra h
      push Not at h
      exact hj (Polynomial.ext h)
    have hjm : j < m := Nat.lt_succ_of_le (Polynomial.le_natDegree_of_ne_zero hj)
    have hin : i < n := lt_of_le_of_lt (Polynomial.le_natDegree_of_ne_zero hi) (hn j)
    exact hi (congrFun hc (⟨i, hin⟩, ⟨j, hjm⟩))
  · rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range] at he
    rw [← Fin.sum_univ_eq_sum_range] at he
    have he' : (∑ j : Fin m, (∑ i : Fin n,
        (p.coeff j.val).coeff i.val • (PowerSeries.X : PowerSeries K) ^ i.val) * B ^ j.val) = 0 := by
      simpa only [polynomial_toSeries_fin _ (hn _)] using he
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simpa only [c, Finset.sum_mul, smul_mul_assoc] using he'

end NonAlgebraicity

#print axioms NonAlgebraicity.hasPolynomialRelation_of_isAlgebraic
