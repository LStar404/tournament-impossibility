import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

noncomputable section
open Metric Set
namespace ComplexCauchyErrorTransfer

/-- A closed disk centered at any point of the smaller disk fits strictly
inside the larger open disk when half the radius gap is used. -/
lemma shifted_closedBall_subset {r R : ℝ} (hgap : r < R) {z : ℂ} (hz : ‖z‖ ≤ r) :
    closedBall z ((R-r)/2) ⊆ ball 0 R := by
  intro w hw
  have hwz : ‖w-z‖ ≤ (R-r)/2 := mem_closedBall_iff_norm.mp hw
  have hnorm := norm_le_norm_sub_add w z
  have hwR : ‖w‖ < R := by linarith
  simpa only [mem_ball, dist_zero_right] using hwR

/-- Fixed-order Cauchy transfer on a smaller disk. Differentiability of the
actual error function and its value bound remain explicit, substantive inputs. -/
theorem derivative_error_half_gap (f : ℂ → ℂ) {r R C : ℝ} (hgap : r < R)
    (hf : DifferentiableOn ℂ f (ball 0 R)) (n j : ℕ)
    (hbound : ∀ w ∈ ball (0 : ℂ) R, ‖f w‖ ≤ C/(n : ℝ))
    {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖iteratedDeriv j f z‖ ≤ (j.factorial : ℝ)*C/((n : ℝ)*((R-r)/2)^j) := by
  have hρ : 0 < (R-r)/2 := by linarith
  have hsub := shifted_closedBall_subset hgap hz
  have hdiff : DiffContOnCl ℂ f (ball z ((R-r)/2)) := hf.diffContOnCl_ball hsub
  have hsphere : ∀ w ∈ sphere z ((R-r)/2), ‖f w‖ ≤ C/(n : ℝ) := by
    intro w hw
    exact hbound w (hsub (sphere_subset_closedBall hw))
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j hρ hdiff hsphere
  convert h using 1 <;> ring

/-- The sharp gap version is available when continuity on the outer closure
is known; otherwise use the half-gap theorem above. -/
theorem derivative_error_full_gap (f : ℂ → ℂ) {r R C : ℝ} (hgap : r < R)
    (hf : DiffContOnCl ℂ f (ball 0 R)) (n j : ℕ)
    (hbound : ∀ w ∈ closedBall (0 : ℂ) R, ‖f w‖ ≤ C/(n : ℝ))
    {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖iteratedDeriv j f z‖ ≤ (j.factorial : ℝ)*C/((n : ℝ)*(R-r)^j) := by
  have hρ : 0 < R-r := sub_pos.mpr hgap
  have hsub : ball z (R-r) ⊆ ball 0 R := by
    intro w hw
    have hwz : ‖w-z‖ < R-r := mem_ball_iff_norm.mp hw
    have hnorm := norm_le_norm_sub_add w z
    have hwR : ‖w‖ < R := by linarith
    simpa only [mem_ball, dist_zero_right] using hwR
  have hsphere : ∀ w ∈ sphere z (R-r), ‖f w‖ ≤ C/(n : ℝ) := by
    intro w hw
    have hwz : ‖w-z‖ = R-r := mem_sphere_iff_norm.mp hw
    have hnorm := norm_le_norm_sub_add w z
    apply hbound w
    have hwR : ‖w‖ ≤ R := by linarith
    simpa only [mem_closedBall, dist_zero_right] using hwR
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j hρ (hf.mono hsub) hsphere
  convert h using 1 <;> ring

/-- Error in the derivatives of two actual analytic functions, not only the
derivative of a formally named difference. -/
theorem derivative_difference_half_gap (f g : ℂ → ℂ) {r R C : ℝ} (hgap : r < R)
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hg : DifferentiableOn ℂ g (ball 0 R))
    (n j : ℕ) (hbound : ∀ w ∈ ball (0 : ℂ) R, ‖f w-g w‖ ≤ C/(n : ℝ))
    {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖iteratedDeriv j f z-iteratedDeriv j g z‖ ≤
      (j.factorial : ℝ)*C/((n : ℝ)*((R-r)/2)^j) := by
  have hzR : z ∈ ball (0 : ℂ) R := by
    simpa only [mem_ball, dist_zero_right] using hz.trans_lt hgap
  have hfA := hf.analyticAt (isOpen_ball.mem_nhds hzR)
  have hgA := hg.analyticAt (isOpen_ball.mem_nhds hzR)
  have h := derivative_error_half_gap (f-g) hgap (hf.sub hg) n j hbound hz
  rw [iteratedDeriv_sub hfA.contDiffAt hgA.contDiffAt] at h
  exact h

end ComplexCauchyErrorTransfer
#print axioms ComplexCauchyErrorTransfer.derivative_error_full_gap
#print axioms ComplexCauchyErrorTransfer.derivative_difference_half_gap
