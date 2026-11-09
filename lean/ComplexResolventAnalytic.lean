import ActualComplexScoreSource

noncomputable section
open scoped Matrix.Norms.L2Operator
namespace ComplexResolventAnalytic
open Matrix DiamondGap DiamondFreeComplexResolvent ActualComplexScoreSource

/-- The true matrix inverse is analytic at every parameter where the
quadratic matrix is a unit. This premise is discharged on fixed disks below. -/
theorem inverse_analyticAt {n : ℕ} (T : Tournament (Fin n)) (w : ℂ)
    (hu : IsUnit (resolventMatrix T w)) :
    AnalyticAt ℂ (fun z => (resolventMatrix T z)⁻¹) w := by
  have hA : AnalyticAt ℂ (fun z => resolventMatrix T z) w := by
    unfold resolventMatrix
    fun_prop
  have hI : AnalyticAt ℂ (fun M : Matrix (Fin n) (Fin n) ℂ => M⁻¹)
      (resolventMatrix T w) := by
    simpa only [Matrix.nonsing_inv_eq_ringInverse, IsUnit.unit_spec] using
      (analyticAt_inverse (𝕜 := ℂ) hu.unit)
  exact hI.comp hA

def sourceFunctional {n : ℕ} (b : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ where
  toFun M := b ⬝ᵥ M.mulVec b
  map_add' M N := by simp [Matrix.add_mulVec,dotProduct_add]
  map_smul' c M := by
    simp [Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]

theorem source_analyticAt {n : ℕ} (T : Tournament (Fin n)) (w : ℂ)
    (hu : IsUnit (resolventMatrix T w)) : AnalyticAt ℂ (source T) w := by
  let L := (sourceFunctional (complexScore T)).toContinuousLinearMap
  have hL : AnalyticAt ℂ L ((resolventMatrix T w)⁻¹) := L.analyticAt _
  have h := hL.comp (f := fun z : ℂ => (resolventMatrix T z)⁻¹) (x := w) (inverse_analyticAt T w hu)
  exact h

/-- A common disk is genuinely analytic for every sufficiently large actual
zero-diamond graph, not an assumed analyticity wrapper around a limit. -/
theorem eventually_analytic_disk {R : ℝ} (hR : 0≤R) (hpi : R<Real.pi/2) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ T : Tournament (Fin n), T.diamonds.card=0 →
      AnalyticOnNhd ℂ (source T) (Metric.closedBall 0 R) := by
  filter_upwards [DiamondFreeDiskResolvent.eventually_uniform_resolvent hR hpi] with n hn
  intro T hT w hw
  have hh := (hn T hT w (by simpa using hw)).1.1
  have hdet := Matrix.isUnit_det_of_right_inverse hh
  exact source_analyticAt T w ((Matrix.isUnit_iff_isUnit_det _).mpr hdet)
end ComplexResolventAnalytic
#print axioms ComplexResolventAnalytic.eventually_analytic_disk
