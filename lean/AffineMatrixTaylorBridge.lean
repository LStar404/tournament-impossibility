import AnalyticTaylorInverse

noncomputable section
namespace AffineMatrixTaylorBridge
open AnalyticTaylorArithmetic AnalyticTaylorFinite AnalyticTaylorInverse
variable {I : Type*} [Fintype I] [DecidableEq I]

def actual (Q : Matrix I I ℂ) (z : ℂ) : Matrix I I ℂ := 1+z • Q

def formal (Q : Matrix I I ℂ) : Matrix I I (PowerSeries ℂ) :=
  1+(PowerSeries.X:PowerSeries ℂ) • Q.map PowerSeries.C

theorem identity_series : series (fun z : ℂ => z)=PowerSeries.X := by
  ext n
  simp only [coeff_series,iteratedDeriv_fun_id_zero,PowerSeries.coeff_X]
  by_cases hn : n=1
  · subst n; simp
  · simp [hn]

theorem analytic_entry (Q : Matrix I I ℂ) (i j : I) :
    AnalyticAt ℂ (fun z => actual Q z i j) 0 := by
  change AnalyticAt ℂ (fun z => (1:Matrix I I ℂ) i j+z*Q i j) 0
  exact analyticAt_const.add (analyticAt_id.mul analyticAt_const)

theorem matrix_series (Q : Matrix I I ℂ) : matrixSeries (actual Q)=formal Q := by
  apply Matrix.ext; intro i j
  change series (fun z => (1:Matrix I I ℂ) i j+z*Q i j)=_
  simp only [Matrix.one_apply]
  erw [add (f:=fun _ : ℂ => if i=j then 1 else 0) (g:=fun z => z*Q i j) analyticAt_const (analyticAt_id.mul analyticAt_const),constant,
    mul (f:=fun z : ℂ => z) (g:=fun _ => Q i j) analyticAt_id analyticAt_const,identity_series,constant]
  simp [formal,Matrix.add_apply,Matrix.smul_apply,Matrix.map_apply,Matrix.one_apply,apply_ite]

theorem inverse_series (Q : Matrix I I ℂ) :
    matrixSeries (fun z => (actual Q z)⁻¹)=(formal Q)⁻¹ := by
  have h0 : (actual Q 0).det≠0 := by simp [actual]
  rw [inverse_transport (actual Q) (analytic_entry Q) h0,matrix_series]

theorem determinant_series (Q : Matrix I I ℂ) :
    series (fun z => (actual Q z).det)=(formal Q).det := by
  rw [determinant (actual Q) (analytic_entry Q),matrix_series]

end AffineMatrixTaylorBridge
#print axioms AffineMatrixTaylorBridge.inverse_series
#print axioms AffineMatrixTaylorBridge.determinant_series
