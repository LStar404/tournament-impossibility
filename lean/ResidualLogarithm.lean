import ResidualScalarActivities
import FormalFirstOrderUniqueness

noncomputable section
namespace ResidualLogarithm
variable {S : Type*} [Field S] [CharZero S] [Algebra ℚ S]

def logarithm : PowerSeries S := PowerSeries.mk (fun n =>
  match n with
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | k+3 => (-1:S)^k/(k+3:S))

theorem constant_logarithm : (logarithm (S:=S)).constantCoeff=0 := by rfl

theorem logarithm_differential :
    (1+PowerSeries.X)*PowerSeries.derivative (logarithm (S:=S))=PowerSeries.X^2 := by
  rw [add_mul,one_mul]
  ext n
  cases n with
  | zero =>
    rw [map_add,PowerSeries.coeff_derivative]
    simp [logarithm,PowerSeries.coeff_X_pow]
  | succ n =>
    simp only [map_add,PowerSeries.coeff_succ_X_mul,PowerSeries.coeff_derivative,
      logarithm,PowerSeries.coeff_mk,PowerSeries.coeff_X_pow]
    rcases n with _ | n
    · norm_num
    rcases n with _ | n
    · norm_num
    have h1 : (n+3:S) ≠ 0 := by exact_mod_cast (show n+3 ≠ 0 by omega)
    have h2 : (n+4:S) ≠ 0 := by exact_mod_cast (show n+4 ≠ 0 by omega)
    have hh : ((-1:S)^(n+1)/(n+4:S))*(n+4:S) +
        ((-1:S)^n/(n+3:S))*(n+3:S) = 0 := by
      rw [div_mul_cancel₀ _ h2,div_mul_cancel₀ _ h1,pow_succ]
      ring
    convert hh using 1 <;> norm_num <;> ring

theorem actual_differential :
    (1+PowerSeries.X)*PowerSeries.derivative (FactorizedResidualIdentity.residual (S:=S) (1:S))=
      PowerSeries.X^2*FactorizedResidualIdentity.residual (S:=S) (1:S) := by
  unfold FactorizedResidualIdentity.residual
  rw [Derivation.leibniz,MixedFormalTimeDerivative.mixed_time_derivative]
  simp only [smul_eq_mul,map_add,map_one,one_pow,smul_eq_mul]
  norm_num
  have hc : (2:PowerSeries S)*PowerSeries.C (1/2:S)=1 := by
    rw [show (2:PowerSeries S)=PowerSeries.C (2:S) from (map_natCast _ 2).symm,← map_mul]
    norm_num
  linear_combination (PowerSeries.X+2*PowerSeries.X^2+PowerSeries.X^3)*
    FormalMixedExponential.mixed (S:=S) (-1:S) (1/2:S)*hc

theorem actual_exp_identity : FactorizedResidualIdentity.residual (S:=S) (1:S)=
    PowerSeries.subst (logarithm (S:=S)) (PowerSeries.exp S) := by
  have hz : ((1:PowerSeries S)+PowerSeries.X).constantCoeff ≠ 0 := by simp
  have hu : ((1:PowerSeries S)+PowerSeries.X)⁻¹*(1+PowerSeries.X)=1 := by
    rw [mul_comm]; exact PowerSeries.mul_inv_cancel _ hz
  have hd := actual_differential (S:=S)
  have hl := logarithm_differential (S:=S)
  have hde : PowerSeries.derivative (PowerSeries.subst (logarithm (S:=S)) (PowerSeries.exp S))=
      PowerSeries.derivative (logarithm (S:=S))*PowerSeries.subst (logarithm (S:=S)) (PowerSeries.exp S) := by
    rw [PowerSeries.derivative_subst (PowerSeries.HasSubst.of_constantCoeff_zero' constant_logarithm),
      PowerSeries.derivative_exp]
    exact mul_comm _ _
  have he : (1+PowerSeries.X)*PowerSeries.derivative (PowerSeries.subst (logarithm (S:=S)) (PowerSeries.exp S))=
      PowerSeries.X^2*PowerSeries.subst (logarithm (S:=S)) (PowerSeries.exp S) := by
    rw [hde,← mul_assoc,hl]
  have hd' := congrArg (fun f : PowerSeries S => (1+PowerSeries.X)⁻¹*f) hd
  have he' := congrArg (fun f : PowerSeries S => (1+PowerSeries.X)⁻¹*f) he
  simp only [← mul_assoc,hu,one_mul] at hd' he'
  apply FormalFirstOrderUniqueness.unique _ _ _ hd' he'
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,ResidualLowCoefficients.residual_zero]
  change 1 = MvPowerSeries.constantCoeff _
  rw [PowerSeries.constantCoeff_subst_of_constantCoeff_zero constant_logarithm]
  simp

end ResidualLogarithm
#print axioms ResidualLogarithm.actual_exp_identity
