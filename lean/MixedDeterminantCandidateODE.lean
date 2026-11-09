import ActualDeterminantBranchDerivative
import MixedSourceQuadraticDerivative
import FormalFirstOrderUniqueness

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.typeDecidableEq
namespace MixedDeterminantCandidateODE
open Matrix ActualMixedSourceWard ActualMixedWardMatrix MixedWardSolution
open MixedCovarianceSymmetry MixedCovarianceDerivative MixedSourceQuadraticDerivative
open ActualMixedDeterminantJacobi ActualDeterminantBranchDerivative FullJacobiDerivation
open ActualMixedSourceTimeODE
variable {I S : Type*} [Fintype I] [Field S] [CharZero S] [Algebra ℚ S]

def traceTerm (K A : I → I → S) : PowerSeries S :=
  ∑ i, ∑ j, PowerSeries.C (A i j) * covariance K A i j

theorem logarithmic_trace (K A : I → I → S) (hA : ∀ i j, A i j = A j i) :
    ((block K A)⁻¹ * entryDerivative PowerSeries.derivative (block K A)).trace =
      2 * PowerSeries.X * traceTerm K A := by
  rw [block_derivative, Matrix.mul_smul, ← Matrix.mul_assoc, Matrix.trace_smul]
  change (2*PowerSeries.X) * ((covariance K A * constantMatrix A).trace) = _
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, constantMatrix, Matrix.of_apply, traceTerm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hA j i, mul_comm]

theorem branch_derivative (K A : I → I → S) (hA : ∀ i j, A i j = A j i) :
    PowerSeries.derivative (determinantBranch K A) =
      -(PowerSeries.X * traceTerm K A) * determinantBranch K A := by
  have hh := branch_differential K A
  rw [logarithmic_trace K A hA] at hh
  have htwo : (2:PowerSeries S) ≠ 0 := by
    intro he
    rw [show (2:PowerSeries S) = PowerSeries.C (2:S) from (map_natCast _ 2).symm] at he
    have hc := congrArg PowerSeries.constantCoeff he
    simp only [PowerSeries.constantCoeff_C, map_zero] at hc
    exact two_ne_zero hc
  apply mul_left_cancel₀ htwo
  linear_combination hh

theorem source_ode_match (K A : I → I → S) (h : I → S)
    (hK : ∀ i j, K i j = K j i) (hA : ∀ i j, A i j = A j i) :
    -(PowerSeries.X * traceTerm K A) + PowerSeries.derivative (source K A h) =
      odeCoefficient K A h := by
  rw [source_derivative K A h hK hA]
  have hq : response K A h ⬝ᵥ (constantMatrix A).mulVec (response K A h) =
      ∑ i, ∑ j, PowerSeries.C (A i j) * response K A h i * response K A h j := by
    simp only [dotProduct, Matrix.mulVec, constantMatrix, Matrix.of_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hq]
  simp only [odeCoefficient, traceTerm, dotProduct, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum, Finset.sum_mul]
  have he (i j : I) : PowerSeries.C (A i j) * (PowerSeries.X^2 * response K A h i * response K A h j) =
      PowerSeries.X^2 * (PowerSeries.C (A i j) * response K A h i * response K A h j) := by ring
  simp only [he, Finset.mul_sum]
  ring

def candidate (K A : I → I → S) (h : I → S) : PowerSeries S :=
  determinantBranch K A * PowerSeries.subst (source K A h) (PowerSeries.exp S)

theorem candidate_derivative (K A : I → I → S) (h : I → S)
    (hK : ∀ i j, K i j = K j i) (hA : ∀ i j, A i j = A j i) :
    PowerSeries.derivative (candidate K A h) = odeCoefficient K A h * candidate K A h := by
  have hz := PowerSeries.HasSubst.of_constantCoeff_zero' (source_constant K A h)
  rw [candidate, Derivation.leibniz, branch_derivative K A hA,
    PowerSeries.derivative_subst hz, PowerSeries.derivative_exp]
  simp only [smul_eq_mul]
  rw [← source_ode_match K A h hK hA]
  ring

end MixedDeterminantCandidateODE
#print axioms MixedDeterminantCandidateODE.candidate_derivative
