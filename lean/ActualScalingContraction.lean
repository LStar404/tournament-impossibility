import ActualMarginalRemainder
import Mathlib.Topology.MetricSpace.Contracting

/-! Verified in the 557-module direct-Lean compilation and declaration audit.
Banach constructs an actual exponential marginal root.
The intermediate linear inverse is assumed here, not scaling existence. A separate
adapter must supply that inverse from density/spectral/balance data. Euclidean
estimates and global permanent asymptotics are deliberately not asserted. -/
set_option autoImplicit false
noncomputable section
namespace ActualScalingContraction
open ActualMarginalRemainder

section Banach
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The actual residual iteration, on the full ambient space. -/
def step (L : E →L[ℝ] E) (f : E) (R : E → E) (z : E) := -L (f+R z)

/-- An explicit small-ball theorem. Its premises contain linear inverse data
and a remainder Lipschitz estimate, but no zero, fixed point, or scaling. -/
theorem exists_gauge_root
    (H G L : E →L[ℝ] E) (f : E) (R : E → E) {a K r : ℝ}
    (ha : 0 ≤ a) (hK : 0 ≤ K) (hr : 0 ≤ r)
    (hL : ‖L‖ ≤ K) (hJL : (H+G)*L = 1) (hGL : G*L = G)
    (hfG : G f = 0) (hRG : ∀ z, G (R z) = 0) (hR0 : R 0 = 0)
    (hR : ∀ z w, ‖z‖ ≤ a → ‖w‖ ≤ a → ‖R z-R w‖ ≤ r*‖z-w‖)
    (hsmall : K*r ≤ 1/2) (hforcing : K*‖f‖ ≤ a/2) :
    ∃ z : E, ‖z‖ ≤ a ∧ G z = 0 ∧ f + H z + R z = 0 := by
  let T := step L f R
  have hTdiff (z w : E) (hz : ‖z‖ ≤ a) (hw : ‖w‖ ≤ a) :
      ‖T z-T w‖ ≤ (1/2:ℝ)*‖z-w‖ := by
    have he : T z-T w = -L (R z-R w) := by
      simp [T, step, map_sub, map_add]
      abel
    rw [he, norm_neg]
    calc
      _ ≤ ‖L‖*‖R z-R w‖ := L.le_opNorm _
      _ ≤ K*(r*‖z-w‖) := mul_le_mul hL (hR z w hz hw) (norm_nonneg _) hK
      _ = (K*r)*‖z-w‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hsmall (norm_nonneg _)
  have hT0 : ‖T 0‖ ≤ a/2 := by
    simpa [T, step, hR0] using
      ((L.le_opNorm f).trans ((mul_le_mul_of_nonneg_right hL (norm_nonneg f)).trans hforcing))
  have hTball (z : E) (hz : ‖z‖ ≤ a) : ‖T z‖ ≤ a := by
    have hd := hTdiff z 0 hz (by simpa using ha)
    have hn := norm_add_le (T z-T 0) (T 0)
    have he : (T z-T 0)+T 0 = T z := sub_add_cancel _ _
    rw [he] at hn
    simp only [sub_zero] at hd
    linarith
  let B := Metric.closedBall (0:E) a
  letI : CompleteSpace B := Metric.isClosed_closedBall.isComplete.completeSpace_coe
  letI : Nonempty B := ⟨⟨0, by simpa [B] using ha⟩⟩
  let TB : B → B := fun z => ⟨T z, by
    have hz : ‖(z:E)‖ ≤ a := by simpa only [B, Metric.mem_closedBall, dist_zero_right] using z.property
    simpa only [B, Metric.mem_closedBall, dist_zero_right] using hTball z hz⟩
  have hcontract : ContractingWith (1/2 : NNReal) TB := by
    constructor
    · norm_num
    · apply LipschitzWith.of_dist_le_mul
      intro z w
      have hz : ‖(z:E)‖ ≤ a := by simpa only [B, Metric.mem_closedBall, dist_zero_right] using z.property
      have hw : ‖(w:E)‖ ≤ a := by simpa only [B, Metric.mem_closedBall, dist_zero_right] using w.property
      simpa [TB, Subtype.dist_eq, dist_eq_norm] using hTdiff z w hz hw
  let zb := ContractingWith.fixedPoint TB hcontract
  let z : E := zb
  have hzfix : T z = z := congrArg Subtype.val hcontract.fixedPoint_isFixedPt
  have hzball : ‖z‖ ≤ a := by simpa only [z, B, Metric.mem_closedBall, dist_zero_right] using zb.property
  have hGLv (v : E) : G (L v) = G v := by
    exact congrArg (fun A : E →L[ℝ] E => A v) hGL
  have hgz : G z = 0 := by
    calc
      G z = G (T z) := congrArg G hzfix.symm
      _ = 0 := by simp [T, step, map_neg, hGLv, map_add, hfG, hRG]
  have hJLv (v : E) : H (L v)+G (L v) = v := by
    exact congrArg (fun A : E →L[ℝ] E => A v) hJL
  have hzEq : (H+G) z = -(f+R z) := by
    calc
      (H+G) z = (H+G) (-L (f+R z)) := congrArg (H+G) hzfix.symm
      _ = -(f+R z) := by
        rw [map_neg]
        exact congrArg Neg.neg (hJLv _)
  have hzEq' : H z = -(f+R z) := by simpa [hgz] using hzEq
  refine ⟨z, hzball, hgz, ?_⟩
  rw [hzEq']
  abel

end Banach

/-- Actual marginal root, with finite entrywise hypotheses and an independently
constructed bounded real inverse. No nonlinear existence premise appears. -/
theorem exists_actual_scaling {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ)
    (G L : V m →L[ℝ] V m) {a S K : ℝ}
    (ha : 0 ≤ a) (hS : 0 ≤ S) (hK : 0 ≤ K)
    (hM : ∀ i j, 0 ≤ M i j)
    (hr : ∀ i, (∑ j, M i j) ≤ S) (hc : ∀ j, (∑ i, M i j) ≤ S)
    (hGker : ∀ z, G z = 0 ↔ signedMass z = 0)
    (hL : ‖L‖ ≤ K) (hJL : (hessian M+G)*L = 1) (hGL : G*L = G)
    (hsmall : K*(2*S*(Real.exp (2*a)-1)) ≤ 1/2)
    (hforcing : K*‖marginals M 0‖ ≤ a/2) :
    ∃ z : V m, ‖z‖ ≤ a ∧ signedMass z = 0 ∧
      (∀ i, (∑ j, M i j*Real.exp (edge z i j)) = 1) ∧
      (∀ j, (∑ i, M i j*Real.exp (edge z i j)) = 1) := by
  have hExp : 0 ≤ Real.exp (2*a)-1 := by
    have := Real.add_one_le_exp (2*a); linarith
  obtain ⟨z, hz, hGz, hroot⟩ := exists_gauge_root
    (hessian M) G L (marginals M 0) (residual M) ha hK (by positivity)
    hL hJL hGL ((hGker _).mpr (signedMass_marginals M 0))
    (fun z => (hGker _).mpr (signedMass_residual M z)) (residual_zero M)
    (fun z w hz hw => residual_sub_bound M hM hS ha hr hc z w hz hw)
    hsmall hforcing
  have hzF : marginals M z = 0 := by
    rw [marginal_decomposition]
    exact hroot
  refine ⟨z, hz, (hGker z).mp hGz, ?_, ?_⟩
  · intro i
    have h := congrArg (fun v : V m => v (Sum.inl i)) hzF
    simpa [marginals, sub_eq_zero] using h
  · intro j
    have h := congrArg (fun v : V m => v (Sum.inr j)) hzF
    simpa [marginals, sub_eq_zero] using h

end ActualScalingContraction
#print axioms ActualScalingContraction.exists_gauge_root
#print axioms ActualScalingContraction.exists_actual_scaling
