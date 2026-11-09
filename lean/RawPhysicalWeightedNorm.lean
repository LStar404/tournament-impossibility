import RawCoordinateDisk
import WeightedCoefficientProducts

noncomputable section
set_option maxHeartbeats 800000
attribute [local instance] Classical.typeDecidableEq
namespace RawPhysicalWeightedNorm
open Matrix RawCoordinateTaylor WeightedCoefficientNorm

theorem bounds {n : ℕ} (hn : 0<n) (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    {rho s q C K : ℝ} (hr : 0 ≤ rho) (hrs : rho<s) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hq : ‖Matrix.toEuclideanCLM (𝕜:=ℂ) Q‖ ≤ q) (hgap : s*q<1)
    (hentry : ∀i j,‖Q i j‖ ≤ C/(n:ℝ))
    (hscore : ∀i,‖(Q.mulVec (fun _ => 1)) i‖ ≤ K/(n:ℝ)) :
    (∀i j,Finite rho (PhysicalTiltedCovariance.covariance Q RawFormalMixedSpecialization.identityInteraction i j) ∧
      norm rho (PhysicalTiltedCovariance.covariance Q RawFormalMixedSpecialization.identityInteraction i j) ≤
        ((s*C+2*s^2*C^2/(1-s*q))/(n:ℝ))/(1-rho/s)) ∧
    (∀i,Finite rho (PhysicalTiltedCovariance.mean Q RawFormalMixedSpecialization.identityInteraction (fun _ => 1) i) ∧
      norm rho (PhysicalTiltedCovariance.mean Q RawFormalMixedSpecialization.identityInteraction (fun _ => 1) i) ≤
        ((s*K+2*s^2*C*K/(1-s*q))/(n:ℝ))/(1-rho/s)) := by
  letI : DecidableEq (Fin n ⊕ Fin n) := Classical.typeDecidableEq _
  have hs : 0<s := hr.trans_lt hrs
  have hpos : 0<1-s*q := by linarith
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hd := RawCoordinateDisk.disk Q hs.le hq hgap
  have hb (z : ℂ) (hz : ‖z‖ ≤ s) := RawBlockNeumannInverse.inverse_bound Q z hz hq hgap
  have hp (z : ℂ) (hz : ‖z‖ ≤ s) := RawBlockInverseScaling.bounds hn Q
    ((1+z • Q)⁻¹) z (by
      convert Matrix.nonsing_inv_mul (AffineMatrixTaylorBridge.actual Q z)
        (Matrix.isUnit_iff_isUnit_det _ |>.mp (hb z hz).1) using 1 <;>
        ext i j <;> simp only [AffineMatrixTaylorBridge.actual,Matrix.mul_apply,Matrix.add_apply,Matrix.one_apply]
        <;> first | (apply Finset.sum_congr rfl; intro a ha; split_ifs <;> rfl) | (split_ifs <;> rfl))
    hC hK hz hentry hscore (hb z hz).2
  constructor
  · intro i j
    have ht := AnalyticTaylorArithmetic.hasSeries (analytic_covariance_zero Q i j)
    have he := congrArg (fun M : Matrix _ _ (PowerSeries ℂ) => M i j) (covariance_series Q)
    change AnalyticTaylorArithmetic.series (fun z => covariance Q z i j)=_ at he
    rw [he] at ht
    apply WeightedCoefficientProducts.analytic_bound hr hrs (by positivity) ht
    · apply DifferentiableOn.diffContOnCl
      erw [closure_ball (0:ℂ) (ne_of_gt hs)]
      exact (hd.1 i j).differentiableOn
    · intro z hz
      have hz' : ‖z‖ ≤ s := by simpa using Metric.sphere_subset_closedBall hz
      simpa [covariance,AffineMatrixTaylorBridge.actual,div_eq_mul_inv,mul_assoc] using (hp z hz').1 i j
  · intro i
    have ha : AnalyticAt ℂ (fun z => mean Q z i) 0 :=
      RawCoordinateDisk.mean_analytic Q 0 (by simp [AffineMatrixTaylorBridge.actual]) i
    have ht := AnalyticTaylorArithmetic.hasSeries ha
    rw [mean_series Q i] at ht
    apply WeightedCoefficientProducts.analytic_bound hr hrs (by positivity) ht
    · apply DifferentiableOn.diffContOnCl
      erw [closure_ball (0:ℂ) (ne_of_gt hs)]
      exact (hd.2 i).differentiableOn
    · intro z hz
      have hz' : ‖z‖ ≤ s := by simpa using Metric.sphere_subset_closedBall hz
      convert (hp z hz').2 i using 1 <;>
        simp [mean,covariance,AffineMatrixTaylorBridge.actual,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm]
end RawPhysicalWeightedNorm
#print axioms RawPhysicalWeightedNorm.bounds
