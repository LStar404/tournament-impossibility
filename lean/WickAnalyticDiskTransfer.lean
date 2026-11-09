import ActualProductWickGerm
import Mathlib.Analysis.Complex.TaylorSeries

noncomputable section
namespace WickAnalyticDiskTransfer

theorem coefficient_identity {f : ℂ → ℂ} {a : ℕ → ℂ}
    (hf : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ a) 0) (k : ℕ) :
    a k=iteratedDeriv k f 0/(k.factorial:ℂ) := by
  have hh := hf.eq_formalMultilinearSeries hf.analyticAt.hasFPowerSeriesAt
  have he := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff k) hh
  simpa only [FormalMultilinearSeries.coeff_ofScalars] using he

/-- Local coefficient identification plus actual holomorphy gives convergence
on the entire open disk, not only analytic continuation of a germ. -/
theorem hasSum_on_disk {f : ℂ → ℂ} {a : ℕ → ℂ} {R : ℝ}
    (hf : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ a) 0)
    (hd : DifferentiableOn ℂ f (Metric.ball 0 R)) {z : ℂ} (hz : ‖z‖<R) :
    HasSum (fun k => a k*z^k) (f z) := by
  have hs := Complex.hasSum_taylorSeries_on_ball hd (by simpa using hz : z∈Metric.ball (0:ℂ) R)
  convert hs using 1
  ext k
  rw [coefficient_identity hf k]
  simp only [sub_zero,smul_eq_mul,div_eq_mul_inv]
  ring

end WickAnalyticDiskTransfer
#print axioms WickAnalyticDiskTransfer.hasSum_on_disk
