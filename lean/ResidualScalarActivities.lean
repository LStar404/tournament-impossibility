import ResidualDegreeAssignments

noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace ResidualScalarActivities
open ResidualDegreeAssignments
variable {S : Type*} [Field S] [CharZero S]

theorem scalar_zero : scalarCoefficient (S:=S) 0=1 := ResidualLowCoefficients.residual_zero _
theorem scalar_one : scalarCoefficient (S:=S) 1=0 := ResidualLowCoefficients.residual_one _
theorem scalar_two : scalarCoefficient (S:=S) 2=0 := ResidualLowCoefficients.residual_two _

theorem scalar_three : scalarCoefficient (S:=S) 3=1/3 := by
  norm_num [scalarCoefficient,FactorizedResidualIdentity.residual,FormalMixedExponential.mixed,
    PowerSeries.coeff_mul,PowerSeries.coeff_expand,Finset.Nat.antidiagonal_succ,
    FormalDividedPowers.divided,PowerSeries.coeff_X]

theorem scalar_four : scalarCoefficient (S:=S) 4= -1/4 := by
  norm_num [scalarCoefficient,FactorizedResidualIdentity.residual,FormalMixedExponential.mixed,
    PowerSeries.coeff_mul,PowerSeries.coeff_expand,Finset.Nat.antidiagonal_succ,
    FormalDividedPowers.divided,PowerSeries.coeff_X]

theorem assignment_zero {I : Type*} [Fintype I] (d : I →₀ ℕ) (i : I)
    (hi : d i=1 ∨ d i=2) : (∏j : I,scalarCoefficient (S:=S) (d j))=0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rcases hi with hi | hi
  · rw [hi,scalar_one]
  · rw [hi,scalar_two]

theorem active_degree {I : Type*} [Fintype I] (d : I →₀ ℕ)
    (hd : (∏j : I,scalarCoefficient (S:=S) (d j)) ≠ 0) (i : I) :
    d i=0 ∨ 3 ≤ d i := by
  have hh : ¬(d i=1 ∨ d i=2) := fun h => hd (assignment_zero d i h)
  omega

/-- Bound on active numerical coordinates, not the later structural vertex count. -/
theorem active_coordinates_bound {I : Type*} [Fintype I] (d : I →₀ ℕ) (m : ℕ)
    (hm : d∈Finset.finsuppAntidiag Finset.univ m)
    (hd : (∏j : I,scalarCoefficient (S:=S) (d j)) ≠ 0) : 3*d.support.card ≤ m := by
  have hs : (∑i∈d.support,d i)=m := by
    rw [← (Finset.mem_finsuppAntidiag.mp hm).1]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i hi hni
    simpa using (Finsupp.notMem_support_iff.mp hni)
  calc
    3*d.support.card = ∑i∈d.support,3 := by simp [mul_comm]
    _ ≤ ∑i∈d.support,d i := by
      apply Finset.sum_le_sum
      intro i hi
      rcases active_degree d hd i with h | h
      · exact False.elim ((Finsupp.mem_support_iff.mp hi) h)
      · exact h
    _ = m := hs

end ResidualScalarActivities
#print axioms ResidualScalarActivities.scalar_four
#print axioms ResidualScalarActivities.active_degree

#print axioms ResidualScalarActivities.active_coordinates_bound
