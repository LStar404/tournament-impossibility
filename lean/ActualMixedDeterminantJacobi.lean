import FullJacobiDerivation
import NormalizedDeterminantBranch

noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace ActualMixedDeterminantJacobi
open ActualMixedWardMatrix MixedWardUnit FullJacobiDerivation
variable {I S : Type*} [Fintype I] [Field S] [CharZero S] [Algebra ℚ S]

theorem actual_jacobi (K A : I → I → S) :
    PowerSeries.derivative (block K A).det = (block K A).det *
      ((block K A)⁻¹ * entryDerivative PowerSeries.derivative (block K A)).trace :=
  unit_jacobi PowerSeries.derivative _ (det_isUnit K A)

def determinantBranch (K A : I → I → S) : PowerSeries S :=
  NormalizedDeterminantBranch.branch (block K A).det

theorem actual_branch_square (K A : I → I → S) :
    (determinantBranch K A)^2 * (block K A).det = 1 :=
  NormalizedDeterminantBranch.branch_square _ (constant_det K A)

theorem actual_branch_constant (K A : I → I → S) :
    (determinantBranch K A).constantCoeff = 1 :=
  NormalizedDeterminantBranch.branch_constant _ (constant_det K A)

end ActualMixedDeterminantJacobi
#print axioms ActualMixedDeterminantJacobi.actual_jacobi
#print axioms ActualMixedDeterminantJacobi.actual_branch_square
