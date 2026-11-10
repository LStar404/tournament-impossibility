import ActualGaussianFinalRateCandidate
/-! Isolated verified exponential bridge. Actual positive determinant main term. -/
set_option autoImplicit false
noncomputable section
namespace GaussianExponentialCandidate
open Matrix RealProjectionAggregationCandidate

lemma inverse_sqrt_eq_exp {d : ℝ} (hd : 0 < d) :
    (Real.sqrt d)⁻¹=Real.exp (-Real.log d/2) := by
  have hs : 0<Real.sqrt d := Real.sqrt_pos.mpr hd
  calc
    (Real.sqrt d)⁻¹=(Real.exp (Real.log (Real.sqrt d)))⁻¹ := by rw [Real.exp_log hs]
    _ = Real.exp (-Real.log (Real.sqrt d)) := (Real.exp_neg _).symm
    _ = Real.exp (-Real.log d/2) := by rw [Real.log_sqrt hd.le]; congr 1; ring

lemma gaussian_main_eq_exp {r c : ℕ} (W : Matrix (Fin r) (Fin c) ℝ)
    (hd : 0<(1-Wᵀ*W).det) :
    (Real.sqrt (1-Wᵀ*W).det)⁻¹=Real.exp (g W) :=
  inverse_sqrt_eq_exp hd

lemma exp_sandwich {x y E : ℝ} (h : ‖x-y‖≤E) :
    Real.exp (y-E)≤Real.exp x ∧ Real.exp x≤Real.exp (y+E) := by
  rw [Real.norm_eq_abs] at h
  have hh := abs_le.mp h
  constructor
  · exact Real.exp_le_exp.mpr (by linarith)
  · exact Real.exp_le_exp.mpr (by linarith)

/-- Algebraic interface for the separate actual p0 theorem. Its absolute error
is preserved additively; no positivity of a lower error-corrected bound is assumed. -/
lemma approximate_main_sandwich {p L y E e : ℝ}
    (hp : |p-L|≤e) (hL : Real.exp (y-E)≤L ∧ L≤Real.exp (y+E)) :
    Real.exp (y-E)-e≤p ∧ p≤Real.exp (y+E)+e := by
  have hh := abs_le.mp hp
  constructor <;> linarith [hL.1, hL.2]
end GaussianExponentialCandidate
