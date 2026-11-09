import AffineMatrixTaylorBridge
import NormalizedDeterminantBranch

noncomputable section
set_option maxHeartbeats 800000
namespace AnalyticTaylorBranch
open AnalyticTaylorArithmetic AnalyticTaylorFinite AffineMatrixTaylorBridge Filter Topology
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem formal_constant (Q : Matrix I I ℂ) : (formal Q).det.constantCoeff=1 := by
  rw [← determinant_series, initial]
  simp [actual]

theorem branch_unique (d f g : PowerSeries ℂ) (hf : f^2*d=1) (hg : g^2*d=1)
    (hf0 : f.constantCoeff=1) (hg0 : g.constantCoeff=1) : f=g := by
  have hd : d≠0 := by intro h; simp [h] at hf
  have hs : f^2=g^2 := mul_right_cancel₀ hd (hf.trans hg.symm)
  have hn : f+g≠0 := by
    intro he
    have hh := congrArg PowerSeries.constantCoeff he
    simp only [map_add,map_zero,hf0,hg0] at hh
    norm_num at hh
  have hm : (f-g)*(f+g)=0 := by calc
    _ = f^2-g^2 := by ring
    _ = 0 := sub_eq_zero.mpr hs
  exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right hn)

/-- A genuine analytic normalized branch has the canonical formal unit branch
as its Taylor series. The square identity is only required as a local identity. -/
theorem branch_series (Q : Matrix I I ℂ) (g : ℂ → ℂ)
    (hg : AnalyticAt ℂ g 0) (hg0 : g 0=1)
    (hs : ∀ᶠ z in 𝓝 (0:ℂ), (g z)^2*(actual Q z).det=1) :
    series g=NormalizedDeterminantBranch.branch (formal Q).det := by
  have hdet := analytic_det (actual Q) (analytic_entry Q)
  have he : series (fun z => (g z*g z)*(actual Q z).det)=1 := by
    have hh : (fun z => (g z*g z)*(actual Q z).det) =ᶠ[𝓝 0] (fun _ => (1:ℂ)) := by
      filter_upwards [hs] with z hz
      simpa only [pow_two] using hz
    rw [congr hh,constant,map_one]
  erw [mul (f:=fun z => g z*g z) (g:=fun z => (actual Q z).det) (hg.mul hg) hdet,
    mul hg hg,determinant_series] at he
  apply branch_unique (formal Q).det (series g) (NormalizedDeterminantBranch.branch (formal Q).det)
  · simpa only [pow_two] using he
  · exact NormalizedDeterminantBranch.branch_square _ (formal_constant Q)
  · simpa using hg0
  · exact NormalizedDeterminantBranch.branch_constant _ (formal_constant Q)

end AnalyticTaylorBranch
#print axioms AnalyticTaylorBranch.branch_series
