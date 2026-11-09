import WickCoefficientCauchy
import Mathlib.Analysis.Normed.Ring.InfiniteSum

noncomputable section
namespace WeightedCoefficientNorm

def mass (rho : ℝ) (F : PowerSeries ℂ) (k : ℕ) : ℝ := ‖F.coeff k‖*rho^k
def norm (rho : ℝ) (F : PowerSeries ℂ) : ℝ := ∑'k,mass rho F k
def Finite (rho : ℝ) (F : PowerSeries ℂ) : Prop := Summable (mass rho F)

theorem nonneg {rho : ℝ} (hr : 0≤rho) (F : PowerSeries ℂ) (k : ℕ) : 0 ≤ mass rho F k :=
  mul_nonneg (norm_nonneg _) (pow_nonneg hr k)

theorem convolution_bound {rho : ℝ} (hr : 0≤rho) (F G : PowerSeries ℂ) (k : ℕ) :
    mass rho (F*G) k ≤ ∑ij∈Finset.HasAntidiagonal.antidiagonal k,mass rho F ij.1*mass rho G ij.2 := by
  unfold mass
  rw [PowerSeries.coeff_mul]
  calc
    _ ≤ (∑ij∈Finset.HasAntidiagonal.antidiagonal k,‖F.coeff ij.1*G.coeff ij.2‖)*rho^k :=
      mul_le_mul_of_nonneg_right (norm_sum_le _ _) (pow_nonneg hr k)
    _ = _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro ij hij
      have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
      rw [← he,pow_add,norm_mul]
      ring

theorem finite_mul {rho : ℝ} (hr : 0≤rho) {F G : PowerSeries ℂ}
    (hF : Finite rho F) (hG : Finite rho G) : Finite rho (F*G) := by
  have hc := summable_sum_mul_antidiagonal_of_summable_mul
    (Summable.mul_of_nonneg hF hG (nonneg hr F) (nonneg hr G))
  exact hc.of_nonneg_of_le (nonneg hr _) (convolution_bound hr F G)

theorem mul_bound {rho : ℝ} (hr : 0≤rho) {F G : PowerSeries ℂ}
    (hF : Finite rho F) (hG : Finite rho G) : norm rho (F*G)≤norm rho F*norm rho G := by
  have hc := summable_sum_mul_antidiagonal_of_summable_mul
    (Summable.mul_of_nonneg hF hG (nonneg hr F) (nonneg hr G))
  have hh := (finite_mul hr hF hG).tsum_le_tsum (convolution_bound hr F G) hc
  have hFn : Summable (fun k => ‖mass rho F k‖) := hF.norm
  have hGn : Summable (fun k => ‖mass rho G k‖) := hG.norm
  rw [← tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hFn hGn] at hh
  exact hh

theorem mass_one (rho : ℝ) (k : ℕ) : mass rho 1 k=if k=0 then 1 else 0 := by
  by_cases hk : k=0 <;> simp [mass,PowerSeries.coeff_one,hk]

theorem finite_one (rho : ℝ) : Finite rho 1 := by
  change Summable (fun k => mass rho 1 k)
  simp_rw [mass_one]
  exact (hasSum_ite_eq (0:ℕ) (1:ℝ)).summable

theorem norm_one (rho : ℝ) : norm rho 1=1 := by
  unfold norm
  simp_rw [mass_one]
  simp

theorem norm_nonnegative {rho : ℝ} (hr : 0≤rho) (F : PowerSeries ℂ) : 0 ≤ norm rho F :=
  tsum_nonneg (nonneg hr F)
end WeightedCoefficientNorm
#print axioms WeightedCoefficientNorm.mul_bound
