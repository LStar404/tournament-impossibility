import WeightedCoefficientSums
import ZeroConstantFormalExp
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
Generic weighted bound for the existing zero-constant formal exponential.
The proof uses finite exponential truncations and loses no radius.
-/
noncomputable section
namespace WeightedFormalExponential
open WeightedCoefficientNorm

lemma finite_power {s : ℝ} (hs : 0 ≤ s) {F : PowerSeries ℂ}
    (hF : Finite s F) (m : ℕ) : Finite s (F^m) := by
  induction m with
  | zero => simpa using finite_one s
  | succ m ih => simpa only [pow_succ] using finite_mul hs ih hF

lemma power_bound {s : ℝ} (hs : 0 ≤ s) {F : PowerSeries ℂ}
    (hF : Finite s F) (m : ℕ) : norm s (F^m) ≤ (norm s F)^m := by
  induction m with
  | zero => simp [norm_one]
  | succ m ih =>
    rw [pow_succ, pow_succ]
    exact (mul_bound hs (finite_power hs hF m) hF).trans
      (mul_le_mul_of_nonneg_right ih (norm_nonnegative hs F))

lemma coefficient_power_zero (F : PowerSeries ℂ) (hF : F.constantCoeff=0)
    (m k : ℕ) (hkm : k < m) : (F^m).coeff k=0 := by
  have hx : (PowerSeries.X : PowerSeries ℂ) ∣ F := PowerSeries.X_dvd_iff.mpr hF
  exact PowerSeries.X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd hx m) k hkm

def truncation (F : PowerSeries ℂ) (N : ℕ) : PowerSeries ℂ :=
  ∑ m ∈ Finset.range N, PowerSeries.C ((PowerSeries.exp ℂ).coeff m)*F^m

lemma truncation_coefficient (F : PowerSeries ℂ) (hF : F.constantCoeff=0)
    (N k : ℕ) (hk : k < N) :
    (ZeroConstantFormalExp.expOf F).coeff k=(truncation F N).coeff k := by
  classical
  have hs : Function.support
      (fun m : ℕ => (PowerSeries.exp ℂ).coeff m • (F^m).coeff k) ⊆
      (Finset.range N : Set ℕ) := by
    intro m hm
    by_contra hn
    have hNm : N ≤ m := by simpa using hn
    have hz := coefficient_power_zero F hF m k (lt_of_lt_of_le hk hNm)
    exact hm (by simp [hz])
  rw [ZeroConstantFormalExp.expOf, PowerSeries.coeff_subst'
    (PowerSeries.HasSubst.of_constantCoeff_zero' hF)]
  rw [finsum_eq_finsetSum_of_support_subset _ hs]
  simp only [truncation, map_sum, PowerSeries.coeff_C_mul, smul_eq_mul]

lemma exp_coefficient_norm (m : ℕ) :
    ‖(PowerSeries.exp ℂ).coeff m‖=1/(m.factorial : ℝ) := by
  simp [PowerSeries.coeff_exp, norm_div, Complex.norm_natCast]

lemma truncation_finite {s : ℝ} (hs : 0 ≤ s) {F : PowerSeries ℂ}
    (hF : Finite s F) (N : ℕ) : Finite s (truncation F N) := by
  apply WeightedCoefficientSums.sum_finite _ _ hs
  intro m hm
  exact WeightedCoefficientSums.scalar_finite s _ _ (finite_power hs hF m)

lemma truncation_bound {s : ℝ} (hs : 0 ≤ s) {F : PowerSeries ℂ}
    (hF : Finite s F) (N : ℕ) :
    norm s (truncation F N) ≤ Real.exp (norm s F) := by
  have hb := WeightedCoefficientSums.sum_norm (Finset.range N)
    (fun m => PowerSeries.C ((PowerSeries.exp ℂ).coeff m)*F^m) hs
    (fun m hm => WeightedCoefficientSums.scalar_finite s _ _ (finite_power hs hF m))
  apply hb.trans
  calc
    _ = ∑ m ∈ Finset.range N, (1/(m.factorial : ℝ))*norm s (F^m) := by
      simp only [WeightedCoefficientSums.scalar_norm, exp_coefficient_norm]
    _ ≤ ∑ m ∈ Finset.range N, (norm s F)^m/(m.factorial : ℝ) := by
      apply Finset.sum_le_sum
      intro m hm
      simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one, one_mul] using
        mul_le_mul_of_nonneg_left (power_bound hs hF m)
          (show 0≤1/(m.factorial : ℝ) by positivity)
    _ ≤ _ := Real.sum_le_exp_of_nonneg (norm_nonnegative hs F) N

/-- The bound concerns the old formal exponential, not a separately defined proxy. -/
theorem bound {s : ℝ} (hs : 0 ≤ s) (F : PowerSeries ℂ)
    (hzero : F.constantCoeff=0) (hF : Finite s F) :
    Finite s (ZeroConstantFormalExp.expOf F) ∧
      norm s (ZeroConstantFormalExp.expOf F) ≤ Real.exp (norm s F) := by
  have hb (N : ℕ) :
      (∑ k ∈ Finset.range N, mass s (ZeroConstantFormalExp.expOf F) k) ≤
        Real.exp (norm s F) := by
    calc
      _ = ∑ k ∈ Finset.range N, mass s (truncation F N) k := by
        apply Finset.sum_congr rfl
        intro k hk
        unfold mass
        rw [truncation_coefficient F hzero N k (Finset.mem_range.mp hk)]
      _ ≤ norm s (truncation F N) :=
        (truncation_finite hs hF N).sum_le_tsum _ (fun k hk => nonneg hs _ k)
      _ ≤ _ := truncation_bound hs hF N
  exact ⟨summable_of_sum_range_le (nonneg hs _) hb,
    Real.tsum_le_of_sum_range_le (nonneg hs _) hb⟩

end WeightedFormalExponential
#print axioms WeightedFormalExponential.bound
