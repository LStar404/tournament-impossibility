import AnalyticTaylorArithmetic

noncomputable section
namespace AnalyticTaylorFinite
open AnalyticTaylorArithmetic

theorem sum {I : Type*} (s : Finset I) (f : I → ℂ → ℂ)
    (hf : ∀ i∈s, AnalyticAt ℂ (f i) 0) :
    series (fun z => ∑ i∈s, f i z)=∑ i∈s,series (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [show (fun z => f a z + ∑ i∈s,f i z)=f a+(fun z => ∑i∈s,f i z) from rfl]
    rw [add (hf a (Finset.mem_insert_self _ _)) (s.analyticAt_fun_sum (fun i hi => hf i (Finset.mem_insert_of_mem hi))), ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

theorem prod {I : Type*} (s : Finset I) (f : I → ℂ → ℂ)
    (hf : ∀ i∈s, AnalyticAt ℂ (f i) 0) :
    series (fun z => ∏ i∈s, f i z)=∏ i∈s,series (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    rw [show (fun z => f a z * ∏ i∈s,f i z)=f a*(fun z => ∏i∈s,f i z) from rfl]
    rw [mul (hf a (Finset.mem_insert_self _ _)) (s.analyticAt_fun_prod (fun i hi => hf i (Finset.mem_insert_of_mem hi))), ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

variable {I : Type*} [Fintype I] [DecidableEq I]
def matrixSeries (M : ℂ → Matrix I I ℂ) : Matrix I I (PowerSeries ℂ) :=
  Matrix.of (fun i j => series (fun z => M z i j))

theorem analytic_det (M : ℂ → Matrix I I ℂ) (hM : ∀ i j, AnalyticAt ℂ (fun z => M z i j) 0) :
    AnalyticAt ℂ (fun z => (M z).det) 0 := by
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  apply Finset.analyticAt_fun_sum
  intro p hp
  exact analyticAt_const.mul (Finset.analyticAt_fun_prod _ (fun i hi => hM (p i) i))

theorem determinant (M : ℂ → Matrix I I ℂ) (hM : ∀ i j, AnalyticAt ℂ (fun z => M z i j) 0) :
    series (fun z => (M z).det)=(matrixSeries M).det := by
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  rw [sum]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [show (fun z => (↑(Equiv.Perm.sign p):ℂ) * ∏ i, M z (p i) i) =
      (fun _ => (↑(Equiv.Perm.sign p):ℂ)) * (fun z => ∏i,M z (p i) i) from rfl]
    rw [mul analyticAt_const (Finset.analyticAt_fun_prod _ (fun i hi => hM (p i) i)),constant,prod _ _ (fun i hi => hM (p i) i)]
    simp [matrixSeries]
  · intro p hp
    exact analyticAt_const.mul (Finset.analyticAt_fun_prod _ (fun i hi => hM (p i) i))

end AnalyticTaylorFinite
#print axioms AnalyticTaylorFinite.determinant
