import FactorizedResidualIdentity

noncomputable section
namespace ResidualLowCoefficients
open FormalDividedPowers FormalMixedExponential FactorizedResidualIdentity
variable {S P : Type*} [Field S] [CharZero S] [CommRing P] [Algebra S P]

theorem residual_zero (a : P) : (residual (S:=S) a).coeff 0=1 := by
  simp [FactorizedResidualIdentity.residual,mixed,PowerSeries.coeff_mul,PowerSeries.coeff_expand,
    Finset.Nat.antidiagonal_zero]

theorem residual_one (a : P) : (residual (S:=S) a).coeff 1=0 := by
  simp [FactorizedResidualIdentity.residual,mixed,PowerSeries.coeff_mul,PowerSeries.coeff_expand,
    Finset.Nat.antidiagonal_succ,Finset.Nat.antidiagonal_zero,divided]

theorem residual_two (a : P) : (residual (S:=S) a).coeff 2=0 := by
  simp [FactorizedResidualIdentity.residual,mixed,PowerSeries.coeff_mul,PowerSeries.coeff_expand,
    Finset.Nat.antidiagonal_succ,Finset.Nat.antidiagonal_zero,divided]
  rw [← add_smul]
  have hh : (2:S)⁻¹+(2:S)⁻¹=1 := by norm_num
  rw [hh]
  simp [PowerSeries.coeff_X,pow_two]

end ResidualLowCoefficients
#print axioms ResidualLowCoefficients.residual_two
