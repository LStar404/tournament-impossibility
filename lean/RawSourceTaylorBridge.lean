import AffineMatrixTaylorBridge
import RawFormalMixedSpecialization

noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace RawSourceTaylorBridge
open Matrix AnalyticTaylorArithmetic AnalyticTaylorFinite AnalyticTaylorInverse AffineMatrixTaylorBridge
variable {I : Type*} [Fintype I]

def sourceMatrix (Q : Matrix I I ℂ) (z : ℂ) := (actual Q z-1)*(actual Q z)⁻¹

def source (Q : Matrix I I ℂ) (z : ℂ) : ℂ :=
  (1/2:ℂ)*((fun _ : I => (1:ℂ)) ⬝ᵥ (sourceMatrix Q z).mulVec (fun _ => 1))

theorem analytic_difference (Q : Matrix I I ℂ) (i j : I) :
    AnalyticAt ℂ (fun z => (actual Q z-1) i j) 0 := by
  convert (analyticAt_id.mul (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => Q i j) 0)) using 1
  ext z
  simp [actual,Matrix.smul_apply]

theorem difference_series (Q : Matrix I I ℂ) :
    matrixSeries (fun z => actual Q z-1)=formal Q-1 := by
  apply Matrix.ext; intro i j
  change series (fun z => (actual Q z-1) i j)=_
  simp only [actual,add_sub_cancel_left,Matrix.smul_apply,smul_eq_mul]
  erw [mul (f:=fun z : ℂ => z) (g:=fun _ => Q i j) analyticAt_id analyticAt_const,
    identity_series,constant]
  simp [formal,Matrix.smul_apply,Matrix.map_apply]

theorem analytic_matrix (Q : Matrix I I ℂ) (i j : I) :
    AnalyticAt ℂ (fun z => sourceMatrix Q z i j) 0 := by
  have h0 : (actual Q 0).det≠0 := by simp [actual]
  unfold sourceMatrix
  simp only [Matrix.mul_apply]
  exact Finset.analyticAt_fun_sum _ (fun k hk =>
    (analytic_difference Q i k).mul (analytic_inverse (actual Q) (analytic_entry Q) h0 k j))

theorem matrix_series (Q : Matrix I I ℂ) :
    matrixSeries (sourceMatrix Q)=(formal Q-1)*(formal Q)⁻¹ := by
  have h0 : (actual Q 0).det≠0 := by simp [actual]
  change matrixSeries (fun z => (actual Q z-1)*(actual Q z)⁻¹)=_
  rw [matrix_mul _ _ (analytic_difference Q) (analytic_inverse (actual Q) (analytic_entry Q) h0),difference_series,inverse_series]

theorem analytic_source (Q : Matrix I I ℂ) : AnalyticAt ℂ (source Q) 0 := by
  unfold source
  simp only [dotProduct,Matrix.mulVec,mul_one,one_mul]
  exact analyticAt_const.mul (Finset.analyticAt_fun_sum _ (fun i hi =>
    Finset.analyticAt_fun_sum _ (fun j hj => analytic_matrix Q i j)))

theorem source_zero (Q : Matrix I I ℂ) : source Q 0=0 := by simp [source,sourceMatrix,actual]

theorem source_series (Q : Matrix I I ℂ) :
    series (source Q)=RawFormalMixedSpecialization.rawSource (formal Q) := by
  have ha := analytic_matrix Q
  have hm := matrix_series Q
  have hm' (i j : I) := congrArg (fun M => M i j) hm
  unfold source RawFormalMixedSpecialization.rawSource
  simp only [dotProduct,Matrix.mulVec,mul_one,one_mul]
  erw [mul (f:=fun _ : ℂ => 1/2) (g:=fun z => ∑i,∑j,sourceMatrix Q z i j)
    analyticAt_const (Finset.analyticAt_fun_sum _ (fun i hi => Finset.analyticAt_fun_sum _ (fun j hj => ha i j))),constant]
  congr 1
  rw [sum _ _ (fun i hi => Finset.analyticAt_fun_sum _ (fun j hj => ha i j))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [sum _ _ (fun j hj => ha i j)]
  apply Finset.sum_congr rfl
  intro j hj
  exact hm' i j

end RawSourceTaylorBridge
#print axioms RawSourceTaylorBridge.source_series
#print axioms RawSourceTaylorBridge.analytic_source
