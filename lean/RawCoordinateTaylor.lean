import AffineMatrixTaylorBridge
import PhysicalTiltedCovariance
import RawFormalMixedSpecialization

noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace RawCoordinateTaylor
open Matrix AnalyticTaylorArithmetic AnalyticTaylorFinite
variable {I : Type*} [Fintype I]

def covariance (Q : Matrix I I ℂ) (z : ℂ) : Matrix I I ℂ :=
  (z • Q)*(AffineMatrixTaylorBridge.actual Q z)⁻¹

def mean (Q : Matrix I I ℂ) (z : ℂ) : I → ℂ := (covariance Q z).mulVec (fun _ => 1)

theorem analytic_inverse_zero (Q : Matrix I I ℂ) (i j : I) :
    AnalyticAt ℂ (fun z => (AffineMatrixTaylorBridge.actual Q z)⁻¹ i j) 0 :=
  AnalyticTaylorInverse.analytic_inverse _ (AffineMatrixTaylorBridge.analytic_entry Q)
    (by simp [AffineMatrixTaylorBridge.actual]) i j

theorem analytic_covariance_zero (Q : Matrix I I ℂ) (i j : I) :
    AnalyticAt ℂ (fun z => covariance Q z i j) 0 := by
  unfold covariance
  simp only [Matrix.mul_apply,Matrix.smul_apply,smul_eq_mul]
  exact Finset.univ.analyticAt_fun_sum (fun k hk =>
    (analyticAt_id.mul analyticAt_const).mul (analytic_inverse_zero Q k j))

theorem covariance_series (Q : Matrix I I ℂ) :
    matrixSeries (covariance Q)=PhysicalTiltedCovariance.covariance Q
      (RawFormalMixedSpecialization.identityInteraction (I:=I) (S:=ℂ)) := by
  unfold covariance
  rw [AnalyticTaylorInverse.matrix_mul]
  · rw [AffineMatrixTaylorBridge.inverse_series]
    have hf : matrixSeries (fun z : ℂ => z • Q)=
        (PowerSeries.X : PowerSeries ℂ) • Q.map PowerSeries.C := by
      apply Matrix.ext; intro i j
      change series (fun z : ℂ => z*Q i j)=_
      erw [mul analyticAt_id analyticAt_const,AffineMatrixTaylorBridge.identity_series,constant]
      rfl
    rw [hf]
    erw [PhysicalTiltedCovariance.raw_covariance]
    rw [Matrix.smul_mul]
    rfl
  · intro i j
    exact analyticAt_id.mul analyticAt_const
  · exact analytic_inverse_zero Q

theorem mean_series (Q : Matrix I I ℂ) (i : I) :
    series (fun z => mean Q z i)=PhysicalTiltedCovariance.mean Q
      (RawFormalMixedSpecialization.identityInteraction (I:=I) (S:=ℂ)) (fun _ => 1) i := by
  change series (fun z => ∑j,covariance Q z i j*1)=_
  simp only [mul_one]
  rw [sum Finset.univ _ (fun j hj => analytic_covariance_zero Q i j)]
  have hh := congrArg (fun M : Matrix I I (PowerSeries ℂ) => ∑j,M i j) (covariance_series Q)
  simpa only [matrixSeries,Matrix.of_apply,PhysicalTiltedCovariance.mean,Matrix.mulVec,
    dotProduct,map_one,mul_one] using hh
end RawCoordinateTaylor
#print axioms RawCoordinateTaylor.covariance_series
#print axioms RawCoordinateTaylor.mean_series
