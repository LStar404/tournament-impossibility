import WeightedCoefficientSums
import Mathlib.Analysis.SpecificLimits.Normed
noncomputable section
namespace WeightedPolynomialMultiplier
open WeightedCoefficientNorm

def moment (t : ℝ) (m : ℕ) : ℝ := ∑'k:ℕ,(k:ℝ)^m*t^k

theorem moment_summable {t : ℝ} (ht : 0 ≤ t) (ht1 : t<1) (m : ℕ) :
    Summable (fun k:ℕ => (k:ℝ)^m*t^k) := by
  have hh := summable_norm_pow_mul_geometric_of_norm_lt_one (R:=ℝ) m
    (show ‖t‖<1 by simpa [Real.norm_eq_abs,abs_of_nonneg ht] using ht1)
  exact hh.of_norm

theorem term_le_moment {t : ℝ} (ht : 0 ≤ t) (ht1 : t<1) (m k : ℕ) :
    (k:ℝ)^m*t^k ≤ moment t m := by
  exact (moment_summable ht ht1 m).le_tsum k (fun i hi => by positivity)

/-- Finite coefficient windows absorb arbitrary fixed polynomial factors using spare radius. -/
theorem finite_window (F : PowerSeries ℂ) (E : Finset ℕ) (m : ℕ)
    (r s sigma : ℝ) (hr : 0 ≤ r) (hs : 0<s) (hsigma : 0 ≤ sigma)
    (hgap : sigma*r<s) (hF : Finite s F) :
    (∑k∈E,(k:ℝ)^m*sigma^k*‖F.coeff k‖*r^k) ≤
      moment (sigma*r/s) m*norm s F := by
  have ht : 0 ≤ sigma*r/s := by positivity
  have ht1 : sigma*r/s<1 := (div_lt_one hs).mpr hgap
  have hm : 0 ≤ moment (sigma*r/s) m := tsum_nonneg (fun k => by positivity)
  calc
    _ = ∑k∈E,((k:ℝ)^m*(sigma*r/s)^k)*mass s F k := by
      apply Finset.sum_congr rfl
      intro k hk
      unfold mass
      simp only [div_pow,mul_pow]
      field_simp
    _ ≤ ∑k∈E,moment (sigma*r/s) m*mass s F k := Finset.sum_le_sum (fun k hk =>
      mul_le_mul_of_nonneg_right (term_le_moment ht ht1 m k) (nonneg hs.le F k))
    _ = moment (sigma*r/s) m*(∑k∈E,mass s F k) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (hF.sum_le_tsum E (fun k hk => nonneg hs.le F k)) hm
end WeightedPolynomialMultiplier
#print axioms WeightedPolynomialMultiplier.finite_window
