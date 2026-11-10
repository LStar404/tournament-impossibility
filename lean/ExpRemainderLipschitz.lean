import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Verified in the 557-module direct-Lean compilation and declaration audit. Scalar exponential remainder; no scaling assumption. -/
set_option autoImplicit false
noncomputable section
namespace ExpRemainderLipschitz

def remainder (t : ℝ) : ℝ := Real.exp t - 1 - t

@[simp] lemma remainder_zero : remainder 0 = 0 := by simp [remainder]

lemma hasDerivAt_remainder (t : ℝ) : HasDerivAt remainder (Real.exp t - 1) t := by
  exact ((Real.hasDerivAt_exp t).sub_const 1).sub (hasDerivAt_id t)

lemma derivative_bound {b t : ℝ} (hb : 0 ≤ b) (ht : t ∈ Set.Icc (-b) b) :
    ‖Real.exp t - 1‖ ≤ Real.exp b - 1 := by
  rw [Real.norm_eq_abs, abs_le]
  have hbt := Real.exp_le_exp.mpr ht.2
  have htExp := Real.add_one_le_exp t
  have hbExp := Real.add_one_le_exp b
  constructor <;> linarith [ht.1]

/-- Direct one-dimensional mean value bound on the closed symmetric interval. -/
theorem remainder_sub_bound {b u v : ℝ} (hb : 0 ≤ b)
    (hu : ‖u‖ ≤ b) (hv : ‖v‖ ≤ b) :
    ‖remainder u - remainder v‖ ≤ (Real.exp b - 1) * ‖u-v‖ := by
  have hu' : u ∈ Set.Icc (-b) b := abs_le.mp hu
  have hv' : v ∈ Set.Icc (-b) b := abs_le.mp hv
  exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (hasDerivAt_remainder t).hasDerivWithinAt)
    (fun t ht => derivative_bound hb ht) (convex_Icc (-b) b) hv' hu'

end ExpRemainderLipschitz
#print axioms ExpRemainderLipschitz.remainder_sub_bound
