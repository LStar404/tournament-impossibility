import RawCoordinateTaylor
import RawBlockNeumannInverse

noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace RawCoordinateDisk
open Matrix RawCoordinateTaylor
open scoped Matrix.Norms.L2Operator
variable {I : Type*} [Fintype I]

def entryFunctional (i j : I) : Matrix I I ℂ →ₗ[ℂ] ℂ where
  toFun M := M i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem inverse_analytic (Q : Matrix I I ℂ) (w : ℂ)
    (hu : IsUnit (AffineMatrixTaylorBridge.actual Q w)) (i j : I) :
    AnalyticAt ℂ (fun z => (AffineMatrixTaylorBridge.actual Q z)⁻¹ i j) w := by
  have hA : AnalyticAt ℂ (AffineMatrixTaylorBridge.actual Q) w := by
    unfold AffineMatrixTaylorBridge.actual
    fun_prop
  have hi : AnalyticAt ℂ (fun M : Matrix I I ℂ => M⁻¹) (AffineMatrixTaylorBridge.actual Q w) := by
    simpa only [Matrix.nonsing_inv_eq_ringInverse,IsUnit.unit_spec] using
      (analyticAt_inverse (𝕜:=ℂ) hu.unit)
  let L := (entryFunctional i j).toContinuousLinearMap
  exact (L.analyticAt _).comp (hi.comp hA)

theorem covariance_analytic (Q : Matrix I I ℂ) (w : ℂ)
    (hu : IsUnit (AffineMatrixTaylorBridge.actual Q w)) (i j : I) :
    AnalyticAt ℂ (fun z => covariance Q z i j) w := by
  unfold covariance
  simp only [Matrix.mul_apply,Matrix.smul_apply,smul_eq_mul]
  exact Finset.univ.analyticAt_fun_sum (fun k hk =>
    (analyticAt_id.mul analyticAt_const).mul (inverse_analytic Q w hu k j))

theorem mean_analytic (Q : Matrix I I ℂ) (w : ℂ)
    (hu : IsUnit (AffineMatrixTaylorBridge.actual Q w)) (i : I) :
    AnalyticAt ℂ (fun z => mean Q z i) w := by
  unfold mean
  simp only [Matrix.mulVec,dotProduct,mul_one]
  exact Finset.univ.analyticAt_fun_sum (fun j hj => covariance_analytic Q w hu i j)

theorem disk (Q : Matrix I I ℂ) {s q : ℝ} (hs : 0 ≤ s)
    (hq : ‖Matrix.toEuclideanCLM (𝕜:=ℂ) Q‖ ≤ q) (hgap : s*q < 1) :
    (∀i j,AnalyticOnNhd ℂ (fun z => covariance Q z i j) (Metric.closedBall 0 s)) ∧
    (∀i,AnalyticOnNhd ℂ (fun z => mean Q z i) (Metric.closedBall 0 s)) := by
  have hu (z : ℂ) (hz : z∈Metric.closedBall 0 s) : IsUnit (AffineMatrixTaylorBridge.actual Q z) :=
    (RawBlockNeumannInverse.inverse_bound Q z (by simpa using hz) hq hgap).1
  exact ⟨fun i j z hz => covariance_analytic Q z (hu z hz) i j,
    fun i z hz => mean_analytic Q z (hu z hz) i⟩
end RawCoordinateDisk
#print axioms RawCoordinateDisk.disk
