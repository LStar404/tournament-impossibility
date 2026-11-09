import OrderedVertexWord

noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace OrderedResidualPolynomial
variable {I S : Type*} [Fintype I] [Field S] [CharZero S] [Algebra ℚ S]

def scalar {b : ℕ} (d : Fin b →₀ ℕ) : S :=
  algebraMap ℚ S (1/(b.factorial:ℚ))*∏v,(ResidualLogarithm.logarithm (S:=S)).coeff (d v)

theorem coefficient (m : ℕ) :
    (FactorizedResidualIdentity.actualResidual (I:=I) (S:=S)).coeff m=
      ∑b∈Finset.range (m/3+1),∑a : Fin b → I,
        ∑d∈Finset.finsuppAntidiag (Finset.univ : Finset (Fin b)) m,
          scalar (S:=S) d • OccurrenceWordDerivative.polynomial (OrderedVertexWord.word d a) := by
  rw [GlobalLogDegreeAssignments.actual_ordered_degrees]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.prod_mul_distrib,← map_prod,OrderedVertexWord.polynomial]
  rw [Algebra.smul_def,scalar,map_mul]
  rw [← IsScalarTower.algebraMap_apply ℚ S (MvPolynomial I S)]
  ring
end OrderedResidualPolynomial
#print axioms OrderedResidualPolynomial.coefficient
