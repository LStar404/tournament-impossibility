import Mathlib

open Filter Topology
namespace AnalyticNormalizedBranch

/-- A common square equation and normalization determine the continuous germ.
No global branch or positive covariance is assumed. -/
theorem eventually_eq {f g d : ℂ → ℂ}
    (hf : ContinuousAt f 0) (hg : ContinuousAt g 0)
    (hf0 : f 0 = 1) (hg0 : g 0 = 1)
    (hsf : ∀ᶠ z in 𝓝 (0:ℂ), (f z)^2*d z=1)
    (hsg : ∀ᶠ z in 𝓝 (0:ℂ), (g z)^2*d z=1) :
    ∀ᶠ z in 𝓝 (0:ℂ), f z=g z := by
  have hn : f 0+g 0 ≠ 0 := by rw [hf0,hg0]; norm_num
  have he := (hf.add hg).eventually_ne hn
  filter_upwards [hsf,hsg,he] with z hz1 hz2 hz3
  have hd : d z ≠ 0 := by intro h; simp [h] at hz1
  have hs : (f z)^2=(g z)^2 := mul_right_cancel₀ hd (hz1.trans hz2.symm)
  have hm : (f z-g z)*(f z+g z)=0 := by calc
    _ = (f z)^2-(g z)^2 := by ring
    _ = 0 := sub_eq_zero.mpr hs
  exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right hz3)

end AnalyticNormalizedBranch
#print axioms AnalyticNormalizedBranch.eventually_eq
