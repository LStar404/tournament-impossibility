import WickAnalyticDiskTransfer
import GaussianSourceAnalytic

noncomputable section
set_option maxHeartbeats 400000
namespace ActualWickUniformDisk
open Filter Topology

def coefficient {n : ℕ} (T : DiamondGap.Tournament (Fin n)) (v : ℂ) (k : ℕ) : ℂ :=
  (TournamentRawFormalWick.series T v).coeff k

theorem norm_branch (v : ℂ) (hv : v^2=1) : ‖v‖≤1 := by
  have hh := congrArg norm hv
  simp only [norm_pow,norm_one] at hh
  nlinarith [norm_nonneg v]

theorem coefficient_germ {n : ℕ} (hn : 0<n) (T : DiamondGap.Tournament (Fin n))
    (hT : T.diamonds.card=0) (v : ℂ) (hv : v^2=1) :
    HasFPowerSeriesAt (GaussianSourceProduct.product T v)
      (FormalMultilinearSeries.ofScalars ℂ (coefficient T v)) 0 := by
  exact ActualProductWickGerm.hasSeries hn T hT v hv

theorem pointwise {n : ℕ} (hn : 0<n) (T : DiamondGap.Tournament (Fin n))
    (hT : T.diamonds.card=0) (v : ℂ) (hv : v^2=1) {s : ℝ}
    (hd : DifferentiableOn ℂ (GaussianSourceProduct.product T v) (Metric.ball 0 s))
    {z : ℂ} (hz : ‖z‖<s) :
    HasSum (fun k => coefficient T v k*z^k) (GaussianSourceProduct.product T v z) :=
  WickAnalyticDiskTransfer.hasSum_on_disk (coefficient_germ hn T hT v hv) hd hz

/-- One order threshold gives convergence of the actual Wick series on every
point of the closed inner disk, for all zero-diamond tournaments. No energy
bound is needed; only the two raw branches v²=1 are asserted. -/
theorem eventually_hasSum {r R : ℝ} (hr : 0≤r) (hrR : r<R) (hR : R<Real.pi/2) :
    ∀ᶠ n : ℕ in atTop, ∀ T : DiamondGap.Tournament (Fin n), T.diamonds.card=0 →
      ∀ v : ℂ, v^2=1 → ∀ z : ℂ, ‖z‖≤r →
        HasSum (fun k => coefficient T v k*z^k) (GaussianSourceProduct.product T v z) := by
  let s := (r+R)/2
  have hs : 0 ≤ s := by dsimp [s]; linarith
  have hrs : r < s := by dsimp [s]; linarith
  have hsR : s < R := by dsimp [s]; linarith
  filter_upwards [GaussianSourceAnalytic.eventually_differentiable_disk hs hsR hR,
    eventually_ge_atTop 1] with n hd hn
  intro T hT v hv z hz
  have hn' : 0<n := by omega
  exact pointwise hn' T hT v hv (hd T hT v (norm_branch v hv)).1 (hz.trans_lt hrs)

theorem eventually_summable {r R : ℝ} (hr : 0≤r) (hrR : r<R) (hR : R<Real.pi/2) :
    ∀ᶠ n : ℕ in atTop, ∀ T : DiamondGap.Tournament (Fin n), T.diamonds.card=0 →
      ∀ v : ℂ, v^2=1 → ∀ z : ℂ, ‖z‖≤r →
        Summable (fun k => coefficient T v k*z^k) := by
  filter_upwards [eventually_hasSum hr hrR hR] with n hn
  intro T hT v hv z hz
  exact (hn T hT v hv z hz).summable

end ActualWickUniformDisk
#print axioms ActualWickUniformDisk.eventually_hasSum
