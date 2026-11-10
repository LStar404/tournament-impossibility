import RawMatrixScalingExistence
import ScalingEpsilonThreshold

/-! Verified in the 557-module direct-Lean compilation and declaration audit.
The raw nonlinear dependencies are covered by the same verified import closure.
Scaling existence retains the theorem's nonnegative-entry, density, marginal-residual,
real centered spectral-gap and positive-threshold hypotheses. -/
set_option autoImplicit false
noncomputable section
namespace RawScalingThreshold
open Matrix ActualMarginalRemainder RawMatrixScalingExistence
open scoped Matrix.Norms.L2Operator
variable {m : ℕ}

def epsilonThreshold (C q : ℝ) : ℝ := ScalingEpsilonThreshold.threshold (rawK C q)

lemma epsilonThreshold_pos {C q : ℝ} (hC : 0 ≤ C) (hq : q < 1) :
    0 < epsilonThreshold C q := by
  apply ScalingEpsilonThreshold.threshold_pos
  unfold rawK
  exact mul_pos (by norm_num) (ScalingEpsilonThreshold.inverse_constant_pos hC hq)

/-- Raw matrix scaling under one positive threshold depending only on C and q.
No inverse, scaling, or separate smallness estimates are supplied by the caller. -/
theorem exists_scaling (hm : 0 < m) (M : Matrix (Fin m) (Fin m) ℝ)
    {C ε q : ℝ} (hC : 0 ≤ C) (hε0 : 0 ≤ ε)
    (hε : ε ≤ epsilonThreshold C q)
    (hM : ∀ i j, 0 ≤ M i j) (hd : ∀ i j, M i j ≤ C/(m : ℝ))
    (hr : ∀ i, |ActualHessianFinite.r M i| ≤ ε)
    (hc : ∀ j, |ActualHessianFinite.c M j| ≤ ε)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hgap : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin m)
      ((1-ActualHessianFinite.P m)*M*(1-ActualHessianFinite.P m))‖ ≤ q) :
    ∃ z : V m, ‖z‖ ≤ 2*rawK C q*ε ∧ signedMass z = 0 ∧
      (∀ i, (∑ j, M i j*Real.exp (edge z i j)) = 1) ∧
      (∀ j, (∑ i, M i j*Real.exp (edge z i j)) = 1) := by
  have hK : 0 < rawK C q := by
    unfold rawK
    exact mul_pos (by norm_num) (ScalingEpsilonThreshold.inverse_constant_pos hC hq1)
  have hs := ScalingEpsilonThreshold.smallness hK
    (show rawK C q = 2*BalancedHessianInverse.inverseConstant (C+4) q from rfl)
    hε0 hε
  exact RawMatrixScalingExistence.exists_scaling hm M hC hε0 hs.1 hM hd hr hc
    hq0 hq1 hgap hs.2.1 hs.2.2

end RawScalingThreshold
#print axioms RawScalingThreshold.epsilonThreshold_pos
#print axioms RawScalingThreshold.exists_scaling
