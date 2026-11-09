import ActualMixedDeterminantJacobi

noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace ActualDeterminantBranchDerivative
open ActualMixedDeterminantJacobi ActualMixedWardMatrix FullJacobiDerivation MixedWardUnit
variable {I S : Type*} [Fintype I] [Field S] [CharZero S] [Algebra ℚ S]

theorem branch_differential (K A : I → I → S) :
    2 * PowerSeries.derivative (determinantBranch K A) + determinantBranch K A *
      ((block K A)⁻¹ * entryDerivative PowerSeries.derivative (block K A)).trace = 0 := by
  let F := determinantBranch K A
  let d := (block K A).det
  let T := ((block K A)⁻¹ * entryDerivative PowerSeries.derivative (block K A)).trace
  have hf : F ≠ 0 := by
    intro he
    have hh := congrArg PowerSeries.constantCoeff he
    simpa [F, actual_branch_constant] using hh
  have hd : d ≠ 0 := by
    intro he
    have hh := congrArg PowerSeries.constantCoeff he
    simpa [d, constant_det] using hh
  have hh := congrArg PowerSeries.derivative (actual_branch_square K A)
  rw [Derivation.leibniz, PowerSeries.derivative_pow, PowerSeries.derivative_one, actual_jacobi] at hh
  simp only [smul_eq_mul] at hh
  have he : F * d * (2 * PowerSeries.derivative F + F*T) = 0 := by
    change (F^2 * (d*T) + d * ((2:ℕ) * F^(2-1) * PowerSeries.derivative F)) = 0 at hh
    convert hh using 1 <;> ring
  exact (mul_eq_zero.mp he).resolve_left (mul_ne_zero hf hd)

end ActualDeterminantBranchDerivative
#print axioms ActualDeterminantBranchDerivative.branch_differential
