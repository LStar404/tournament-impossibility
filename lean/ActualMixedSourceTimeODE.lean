import MixedFormalTimeDerivative
import MixedWardSolution
import PairingMomentParity

noncomputable section
open scoped BigOperators
namespace ActualMixedSourceTimeODE
open ActualMixedSourceWard FormalWickInsertion FormalMixedExponential FormalDividedPowers
open MixedSourcePolynomials MixedFormalTimeDerivative OccurrenceWickPolynomial
variable {I S : Type*} [Fintype I] [Field S] [CharZero S]

theorem wick_one (K : I → I → S) (hs : ∀ i j, K i j = K j i) : wick K hs 1 = 1 := by
  have he : MvPolynomial.monomial (0 : I →₀ ℕ) (1:S) = 1 := by simp
  rw [← he, wick_monomial, one_mul]
  letI : IsEmpty (Occ (0 : I →₀ ℕ)) := ⟨fun x => by
    have hx : x.2.val < 0 := by simpa using x.2.isLt
    omega⟩
  exact PairingMomentParity.empty_moment_one _ _

theorem Z_initial (K : I → I → S) (hs : ∀ i j, K i j = K j i)
    (h : I → S) (A : I → I → S) : (Z K hs h A).constantCoeff = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [Z, E, coeff_moment, mixed, exponential, divided, wick_one]

theorem Z_derivative (K : I → I → S) (hs : ∀ i j, K i j = K j i)
    (h : I → S) (A : I → I → S) :
    PowerSeries.derivative (Z K hs h A) =
      (∑ i, PowerSeries.C (h i) * G K hs h A i) -
      PowerSeries.X * ∑ i, ∑ j, PowerSeries.C (A i j) * H K hs h A i j := by
  change PowerSeries.derivative (FormalLinearLift.lift _ (E h A)) = _
  rw [lift_time_derivative]
  change moment K hs 1 (PowerSeries.derivative (E h A)) = _
  rw [E, mixed_time_derivative]
  change moment K hs 1 ((PowerSeries.C (LinearSourceExpansion.source h) +
      2 * PowerSeries.X * PowerSeries.C (interaction A)) * E h A) = _
  have he : (2 : PowerSeries (MvPolynomial I S)) * PowerSeries.X * PowerSeries.C (interaction A) =
      PowerSeries.X * PowerSeries.C (2 * interaction A) := by
    rw [map_mul, show PowerSeries.C (2 : MvPolynomial I S) = 2 from map_natCast _ 2]
    ring
  rw [he, add_mul, moment_add, moment_C_mul, one_mul]
  have hx : moment K hs 1 (PowerSeries.X * (PowerSeries.C (2 * interaction A) * E h A)) =
      PowerSeries.X * moment K hs 1 (PowerSeries.C (2 * interaction A) * E h A) := by
    simpa using moment_shift K hs 1 (PowerSeries.C (2 * interaction A) * E h A) 1
  rw [mul_assoc, hx, moment_C_mul, one_mul]
  have hp : 2 * interaction A = -(∑ i, ∑ j, A i j • (MvPolynomial.X i * MvPolynomial.X j)) := by
    unfold interaction
    rw [two_mul, ← add_smul]
    norm_num
  rw [hp]
  have hn (Q : MvPolynomial I S) : moment K hs (-Q) (E h A) = -moment K hs Q (E h A) := by ext n; simp
  rw [hn]
  simp only [LinearSourceExpansion.source, moment_sum_insert, moment_smul_insert]
  change _ = (∑ i, PowerSeries.C (h i) * moment K hs (MvPolynomial.X i) (E h A)) - _
  simp only [G, H]
  ring

def odeCoefficient (K A : I → I → S) (h : I → S) : PowerSeries S :=
  (∑ i, PowerSeries.C (h i) * (PowerSeries.X * MixedWardSolution.response K A h i)) -
  PowerSeries.X * ∑ i, ∑ j, PowerSeries.C (A i j) *
    (MixedWardSolution.covariance K A i j +
      PowerSeries.X^2 * MixedWardSolution.response K A h i * MixedWardSolution.response K A h j)

/-- Actual source ODE, with the true inverse established rather than assumed. -/
theorem scalar_ode (K : I → I → S) (hs : ∀ i j, K i j = K j i)
    (h : I → S) (A : I → I → S) (hA : ∀ i j, A i j = A j i) :
    PowerSeries.derivative (Z K hs h A) = odeCoefficient K A h * Z K hs h A := by
  rw [Z_derivative]
  simp_rw [MixedWardSolution.G_solution K hs h A hA, MixedWardSolution.H_solution K hs h A hA]
  simp only [odeCoefficient, sub_mul, Finset.sum_mul, add_mul, mul_add, mul_assoc]

end ActualMixedSourceTimeODE
#print axioms ActualMixedSourceTimeODE.Z_initial
#print axioms ActualMixedSourceTimeODE.Z_derivative

#print axioms ActualMixedSourceTimeODE.scalar_ode
