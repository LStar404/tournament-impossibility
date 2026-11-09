import ZeroConstantFormalExp
import ResidualLogFiniteVertices
import ResidualHomogeneity

noncomputable section
namespace GlobalResidualLog
open ZeroConstantFormalExp
variable {S P : Type*} [Field S] [CharZero S] [Algebra ℚ S]
    [CommRing P] [Algebra S P] [Algebra ℚ P]

def localLog (a : P) : PowerSeries P := PowerSeries.rescale a
  (PowerSeries.map (algebraMap S P) (ResidualLogarithm.logarithm (S:=S)))

theorem local_constant (a : P) : (localLog (S:=S) a).constantCoeff=0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [localLog,PowerSeries.coeff_rescale,PowerSeries.coeff_map,ResidualLogarithm.logarithm]

theorem local_identity (a : P) : FactorizedResidualIdentity.residual (S:=S) a=
    expOf (localLog (S:=S) a) := by
  rw [← ResidualHomogeneity.rescale_residual,← ResidualHomogeneity.map_residual_one,
    ResidualLogarithm.actual_exp_identity]
  have hm := PowerSeries.map_subst
    (PowerSeries.HasSubst.of_constantCoeff_zero' (ResidualLogarithm.constant_logarithm (S:=S)))
    (h:=algebraMap S P) (PowerSeries.exp S)
  change PowerSeries.rescale a (PowerSeries.map (algebraMap S P)
    ((PowerSeries.exp S).subst (ResidualLogarithm.logarithm (S:=S))))=_
  erw [hm]
  rw [PowerSeries.map_exp]
  unfold expOf localLog
  rw [PowerSeries.rescale_eq_subst,PowerSeries.rescale_eq_subst]
  exact PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero' (by
      change (PowerSeries.map (algebraMap S P) (ResidualLogarithm.logarithm (S:=S))).constantCoeff=0
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
      simp [PowerSeries.coeff_map,ResidualLogarithm.logarithm]))
    (PowerSeries.HasSubst.smul_X' a) _

theorem finite_identity {I : Type*} (s : Finset I) (a : I → P) :
    (∏i∈s,FactorizedResidualIdentity.residual (S:=S) (a i))=
      expOf (∑i∈s,localLog (S:=S) (a i)) := by
  rw [finite_sum _ _ (fun i hi => local_constant _)]
  exact Finset.prod_congr rfl (fun i hi => local_identity _)

theorem actual_identity {I : Type*} [Fintype I] :
    FactorizedResidualIdentity.actualResidual (I:=I) (S:=S)=
      expOf (∑i:I,localLog (S:=S) (MvPolynomial.X i)) := by
  exact finite_identity Finset.univ _
end GlobalResidualLog
#print axioms GlobalResidualLog.actual_identity
