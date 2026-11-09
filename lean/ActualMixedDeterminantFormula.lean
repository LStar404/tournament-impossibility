import MixedDeterminantCandidateODE

noncomputable section
namespace ActualMixedDeterminantFormula
open ActualMixedSourceWard ActualMixedSourceTimeODE MixedDeterminantCandidateODE
open ActualMixedDeterminantJacobi MixedSourceQuadraticDerivative
variable {I S : Type*} [Fintype I] [Field S] [CharZero S] [Algebra ℚ S]

theorem candidate_initial (K A : I → I → S) (h : I → S) :
    (candidate K A h).constantCoeff = 1 := by
  rw [candidate, map_mul, actual_branch_constant, one_mul]
  change MvPowerSeries.constantCoeff (PowerSeries.subst (source K A h) (PowerSeries.exp S)) = 1
  rw [PowerSeries.constantCoeff_subst_of_constantCoeff_zero (source_constant K A h)]
  simp

/-- Actual mixed full Wick series equals the normalized determinant branch
 times the formal exponential of the actual inverse-quadratic source. -/
theorem actual_formula (K : I → I → S) (hK : ∀ i j, K i j = K j i)
    (A : I → I → S) (hA : ∀ i j, A i j = A j i) (h : I → S) :
    Z K hK h A = determinantBranch K A *
      PowerSeries.subst (source K A h) (PowerSeries.exp S) := by
  apply FormalFirstOrderUniqueness.unique (odeCoefficient K A h)
  · exact scalar_ode K hK h A hA
  · exact candidate_derivative K A h hK hA
  · rw [Z_initial]
    exact (candidate_initial K A h).symm

end ActualMixedDeterminantFormula
#print axioms ActualMixedDeterminantFormula.actual_formula
