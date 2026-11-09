import AnalyticTaylorFinite

noncomputable section
namespace AnalyticTaylorInverse
open AnalyticTaylorArithmetic AnalyticTaylorFinite Filter Topology
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem analytic_adjugate (M : ℂ → Matrix I I ℂ)
    (hM : ∀ i j, AnalyticAt ℂ (fun z => M z i j) 0) (i j : I) :
    AnalyticAt ℂ (fun z => (M z).adjugate i j) 0 := by
  simp only [Matrix.adjugate_apply]
  apply analytic_det (fun z => (M z).updateRow j (Pi.single i 1))
  intro a b
  by_cases ha : a=j
  · subst a; simpa [Matrix.updateRow_self] using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => ((Pi.single i (1:ℂ) : I → ℂ) b)) 0)
  · simpa [Matrix.updateRow_apply, ha] using hM a b

theorem analytic_inverse (M : ℂ → Matrix I I ℂ)
    (hM : ∀ i j, AnalyticAt ℂ (fun z => M z i j) 0) (h0 : (M 0).det≠0) (i j : I) :
    AnalyticAt ℂ (fun z => (M z)⁻¹ i j) 0 := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
  exact ((analytic_det M hM).inv h0).mul (analytic_adjugate M hM i j)

theorem matrix_mul (M N : ℂ → Matrix I I ℂ)
    (hM : ∀ i j, AnalyticAt ℂ (fun z => M z i j) 0)
    (hN : ∀ i j, AnalyticAt ℂ (fun z => N z i j) 0) :
    matrixSeries (fun z => M z*N z)=matrixSeries M * matrixSeries N := by
  apply Matrix.ext; intro i j
  change series (fun z => ∑k,M z i k*N z k j)=_
  rw [sum Finset.univ (fun k z => M z i k*N z k j) (fun k hk => (hM i k).mul (hN k j))]
  simp only [Matrix.mul_apply,matrixSeries,Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro k hk
  exact mul (hM i k) (hN k j)

theorem inverse_transport (M : ℂ → Matrix I I ℂ)
    (hM : ∀ i j, AnalyticAt ℂ (fun z => M z i j) 0) (h0 : (M 0).det≠0) :
    matrixSeries (fun z => (M z)⁻¹)=(matrixSeries M)⁻¹ := by
  have hu : IsUnit (matrixSeries M).det := by
    rw [← determinant M hM, PowerSeries.isUnit_iff_constantCoeff,initial]
    exact isUnit_iff_ne_zero.mpr h0
  have he : ∀ᶠ z in 𝓝 (0:ℂ), (M z).det≠0 := (analytic_det M hM).continuousAt.eventually_ne h0
  have hm : matrixSeries (fun z => M z*(M z)⁻¹)=1 := by
    apply Matrix.ext; intro i j
    change series (fun z => (M z*(M z)⁻¹) i j) = _
    have hh : (fun z => (M z*(M z)⁻¹) i j) =ᶠ[𝓝 0] (fun _ => (1:Matrix I I ℂ) i j) := by
      filter_upwards [he] with z hz
      rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hz)]
    rw [congr hh,constant]
    simp [Matrix.one_apply,apply_ite]
  rw [matrix_mul M (fun z => (M z)⁻¹) hM (analytic_inverse M hM h0)] at hm
  have hh := congrArg (fun N => (matrixSeries M)⁻¹*N) hm
  simpa only [← Matrix.mul_assoc,Matrix.nonsing_inv_mul _ hu,Matrix.one_mul,Matrix.mul_one] using hh

end AnalyticTaylorInverse
#print axioms AnalyticTaylorInverse.inverse_transport
