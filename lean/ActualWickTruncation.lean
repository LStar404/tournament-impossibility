import WickGeometricTruncation

noncomputable section
namespace ActualWickTruncation
open Filter Topology ActualWickUniformDisk ActualWickCoefficientBounds

/-- A uniform true remainder bound for the analytic Gaussian/Wick core.
This is not a tail bound for the finite matching/permanent polynomial. -/
theorem eventually_remainder {ρ s R K : ℝ} (hρ : 0 ≤ ρ) (hρs : ρ < s)
    (hsR : s < R) (hR : R < Real.pi/2) (hK : 0 ≤ K) :
    ∀ᶠ n : ℕ in atTop, ∀ T : DiamondGap.Tournament (Fin n), T.diamonds.card=0 →
      ActualComplexScoreSource.scoreEnergy T ≤ K*(n:ℝ) → ∀ v : ℂ, v^2=1 →
      ∀ m : ℕ, ∀ z : ℂ, ‖z‖ ≤ ρ →
      ‖GaussianSourceProduct.product T v z-∑k∈Finset.range m,coefficient T v k*z^k‖
        ≤ bound s R K*(ρ/s)^m/(1-ρ/s) := by
  obtain ⟨hM,hcoeff⟩ := eventually_coefficients (hρ.trans_lt hρs) hsR hR hK
  filter_upwards [hcoeff,eventually_hasSum hρ (hρs.trans hsR) hR] with n hn hsum
  intro T hT hE v hv m z hz
  exact WickGeometricTruncation.remainder_bound hρ hρs hM (hn T hT hE v hv)
    hz (hsum T hT v hv z hz) m

end ActualWickTruncation
#print axioms ActualWickTruncation.eventually_remainder
