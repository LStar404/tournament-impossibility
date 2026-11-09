import AnalyticTaylorBranch
import FormalFirstOrderUniqueness

noncomputable section
namespace TaylorDerivativeExponential
open AnalyticTaylorArithmetic Filter Topology

theorem derivative_series (f : ℂ → ℂ) :
    PowerSeries.derivative (series f)=series (deriv f) := by
  ext n
  simp only [PowerSeries.coeff_derivative,coeff_series,iteratedDeriv_succ',Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  have hn : (n:ℂ)+1≠0 := by exact_mod_cast Nat.succ_ne_zero n
  field_simp

theorem exp_series (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (h0 : f 0=0) :
    series (fun z => Complex.exp (f z)) =
      PowerSeries.subst (series f) (PowerSeries.exp ℂ) := by
  have he : AnalyticAt ℂ (fun z => Complex.exp (f z)) 0 := hf.cexp'
  have hd : AnalyticAt ℂ (deriv f) 0 := hf.deriv
  have hc : deriv (fun z => Complex.exp (f z)) =ᶠ[𝓝 0]
      (fun z => deriv f z * Complex.exp (f z)) := by
    filter_upwards [hf.eventually_analyticAt] with z hz
    simpa only [mul_comm] using hz.differentiableAt.hasDerivAt.cexp.deriv
  have hODE : PowerSeries.derivative (series (fun z => Complex.exp (f z))) =
      PowerSeries.derivative (series f)*series (fun z => Complex.exp (f z)) := by
    rw [derivative_series,congr hc]
    erw [mul hd he,derivative_series]
  have hz : (series f).constantCoeff=0 := by simpa using h0
  have hs : PowerSeries.derivative (PowerSeries.subst (series f) (PowerSeries.exp ℂ)) =
      PowerSeries.derivative (series f)*PowerSeries.subst (series f) (PowerSeries.exp ℂ) := by
    rw [PowerSeries.derivative_subst (PowerSeries.HasSubst.of_constantCoeff_zero' hz),PowerSeries.derivative_exp]
    exact mul_comm _ _
  apply FormalFirstOrderUniqueness.unique (PowerSeries.derivative (series f)) _ _ hODE hs
  rw [initial,h0,Complex.exp_zero]
  change 1 = MvPowerSeries.constantCoeff (PowerSeries.subst (series f) (PowerSeries.exp ℂ))
  rw [PowerSeries.constantCoeff_subst_of_constantCoeff_zero hz]
  simp

end TaylorDerivativeExponential
#print axioms TaylorDerivativeExponential.exp_series
