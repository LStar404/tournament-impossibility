import ResidualLowCoefficients

noncomputable section
namespace ResidualHomogeneity
open FormalDividedPowers FormalMixedExponential FactorizedResidualIdentity
variable {S P : Type*} [Field S] [CharZero S] [CommRing P] [Algebra S P]

theorem rescale_exponential (a b : P) :
    PowerSeries.rescale a (exponential (S:=S) b)=exponential (S:=S) (a*b) := by
  ext n
  simp [divided,mul_pow,Algebra.smul_def,mul_assoc,mul_left_comm]

theorem rescale_quadratic (a : P) (F : PowerSeries P) :
    PowerSeries.rescale a (PowerSeries.expand 2 (by decide) F)=
      PowerSeries.expand 2 (by decide) (PowerSeries.rescale (a^2) F) := by
  ext n
  simp only [PowerSeries.coeff_rescale,PowerSeries.coeff_expand]
  split_ifs with h
  · rw [← pow_mul,Nat.mul_div_cancel' h]
  · simp

theorem rescale_mixed (a b c : P) :
    PowerSeries.rescale a (mixed (S:=S) b c)=mixed (S:=S) (a*b) (a^2*c) := by
  simp only [mixed,map_mul,rescale_exponential,rescale_quadratic]

theorem rescale_residual (a : P) :
    PowerSeries.rescale a (FactorizedResidualIdentity.residual (S:=S) (1:P))=
      FactorizedResidualIdentity.residual (S:=S) a := by
  simp only [FactorizedResidualIdentity.residual,map_mul,map_add,map_one,
    show PowerSeries.C (1:P)=1 from map_one _,PowerSeries.rescale_X,
    rescale_mixed,mul_one,pow_one,one_pow,one_mul,mul_neg]
  congr 2
  simp [Algebra.smul_def,mul_comm]

theorem map_exponential (b : S) :
    PowerSeries.map (algebraMap S P) (exponential (S:=S) b)=
      exponential (S:=S) (algebraMap S P b) := by
  ext n
  simp [divided,Algebra.smul_def]

theorem map_mixed (b c : S) :
    PowerSeries.map (algebraMap S P) (mixed (S:=S) b c)=
      mixed (S:=S) (algebraMap S P b) (algebraMap S P c) := by
  simp only [mixed,map_mul,PowerSeries.map_expand,map_exponential]

theorem map_residual_one :
    PowerSeries.map (algebraMap S P) (FactorizedResidualIdentity.residual (S:=S) (1:S))=
      FactorizedResidualIdentity.residual (S:=S) (1:P) := by
  simp only [FactorizedResidualIdentity.residual,map_mul,map_add,map_one,PowerSeries.map_C,
    PowerSeries.map_X,map_mixed,map_neg,one_pow,Algebra.smul_def]
  simp

/-- Homogeneity of the actual residual coefficients, proved by actual rescaling. -/
theorem coefficient (a : P) (m : ℕ) :
    (FactorizedResidualIdentity.residual (S:=S) a).coeff m =
      ((FactorizedResidualIdentity.residual (S:=S) (1:S)).coeff m) • a^m := by
  rw [← rescale_residual,PowerSeries.coeff_rescale,← map_residual_one,
    PowerSeries.coeff_map]
  simp [Algebra.smul_def,mul_comm]

end ResidualHomogeneity
#print axioms ResidualHomogeneity.coefficient
