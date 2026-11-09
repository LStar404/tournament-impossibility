import WeightedCoefficientProducts
noncomputable section
namespace WeightedCoefficientSums
open WeightedCoefficientNorm

theorem scalar_mass (rho : ℝ) (c : ℂ) (F : PowerSeries ℂ) (k : ℕ) :
    mass rho (PowerSeries.C c*F) k=‖c‖*mass rho F k := by
  simp [mass,PowerSeries.coeff_C_mul,norm_mul,mul_assoc]

theorem scalar_finite (rho : ℝ) (c : ℂ) (F : PowerSeries ℂ) (hf : Finite rho F) :
    Finite rho (PowerSeries.C c*F) := by
  change Summable (fun k => mass rho (PowerSeries.C c*F) k)
  simp_rw [scalar_mass]
  exact hf.mul_left _

theorem scalar_norm (rho : ℝ) (c : ℂ) (F : PowerSeries ℂ) :
    norm rho (PowerSeries.C c*F)=‖c‖*norm rho F := by
  unfold WeightedCoefficientNorm.norm
  simp_rw [scalar_mass]
  exact tsum_mul_left

theorem finite_zero (rho : ℝ) : Finite rho 0 := by
  change Summable (fun k => mass rho (0:PowerSeries ℂ) k)
  simp [mass]

theorem norm_zero (rho : ℝ) : norm rho 0=0 := by simp [WeightedCoefficientNorm.norm,mass]

theorem sum_mass {J : Type*} (t : Finset J) (f : J → PowerSeries ℂ)
    {rho : ℝ} (hr : 0 ≤ rho) (k : ℕ) :
    mass rho (∑i∈t,f i) k ≤ ∑i∈t,mass rho (f i) k := by
  unfold mass
  rw [map_sum,← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (norm_sum_le _ _) (pow_nonneg hr k)

theorem sum_finite {J : Type*} (t : Finset J) (f : J → PowerSeries ℂ)
    {rho : ℝ} (hr : 0 ≤ rho) (hf : ∀i∈t,Finite rho (f i)) :
    Finite rho (∑i∈t,f i) := by
  have hs : Summable (fun k => ∑i∈t,mass rho (f i) k) := summable_sum hf
  exact hs.of_nonneg_of_le (nonneg hr _) (sum_mass t f hr)

theorem sum_norm {J : Type*} (t : Finset J) (f : J → PowerSeries ℂ)
    {rho : ℝ} (hr : 0 ≤ rho) (hf : ∀i∈t,Finite rho (f i)) :
    norm rho (∑i∈t,f i) ≤ ∑i∈t,norm rho (f i) := by
  have hs : Summable (fun k => ∑i∈t,mass rho (f i) k) := summable_sum hf
  have h := (sum_finite t f hr hf).tsum_le_tsum (sum_mass t f hr) hs
  rw [Summable.tsum_finsetSum hf] at h
  exact h
end WeightedCoefficientSums
#print axioms WeightedCoefficientSums.sum_norm
