import Mathlib

/-!
Standalone abstract backend component; final evidence: focused/result.json.
This proves the sparse harmonic series exactly from Mathlib's logarithm
series and injective reindexing. The endpoint correction is then computed
from an exact finite geometric factorization. No log asymptotic is assumed.
-/
noncomputable section
open Filter Topology Finset
namespace FJSparseHarmonic

def sparseTerm (q : ℕ) (z : ℂ) (n : ℕ) : ℂ :=
  if q ∣ n then z^n / (n : ℂ) else 0

def sparseHarmonic (q : ℕ) (z : ℂ) : ℂ := ∑' n, sparseTerm q z n

/-- The n=0 term is exactly zero because division by zero is total in Lean.
All nonzero terms are obtained once through the injection m ↦ q*m. -/
theorem hasSum_sparse_harmonic (q : ℕ) (hq : 0 < q) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (sparseTerm q z) (-Complex.log (1-z^q)/(q : ℂ)) := by
  have hi : Function.Injective (fun n : ℕ => q*n) := by
    intro m n h
    exact mul_left_cancel₀ (by omega : q ≠ 0) h
  have ho : ∀ n : ℕ, n ∉ Set.range (fun m : ℕ => q*m) → sparseTerm q z n=0 := by
    intro n hn
    have hndiv : ¬ q ∣ n := by
      rintro ⟨m, hm⟩
      exact hn ⟨m, hm.symm⟩
    simp [sparseTerm, hndiv]
  have hzq : ‖z^q‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg z) hz (by omega)
  have hs := (Complex.hasSum_taylorSeries_neg_log hzq).mul_left ((q : ℂ)⁻¹)
  have hs' : HasSum (fun n : ℕ => sparseTerm q z (q*n))
      (-Complex.log (1-z^q)/(q : ℂ)) := by
    convert hs using 1
    · ext n
      simp [sparseTerm, pow_mul, Nat.cast_mul, div_eq_mul_inv,
        mul_comm, mul_left_comm]
    · simp [div_eq_mul_inv, mul_comm]
  exact (hi.hasSum_iff ho).mp hs'

theorem sparse_harmonic_eq (q : ℕ) (hq : 0 < q) {z : ℂ} (hz : ‖z‖ < 1) :
    sparseHarmonic q z = -Complex.log (1-z^q)/(q : ℂ) :=
  (hasSum_sparse_harmonic q hq hz).tsum_eq

/-- The logarithm is real on the positive radial interval. -/
theorem sparse_harmonic_real_eq (q : ℕ) (hq : 0 < q) {x : ℝ}
    (hx : x ∈ Set.Ioo 0 1) :
    sparseHarmonic q (x : ℂ) = -(Real.log (1-x^q) : ℂ)/(q : ℂ) := by
  have hxq : x^q < 1 := pow_lt_one₀ hx.1.le hx.2 (by omega)
  have hcast : 1-(x : ℂ)^q = ((1-x^q : ℝ) : ℂ) := by push_cast; rfl
  rw [sparse_harmonic_eq q hq
    (by simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx.1] using hx.2),
    hcast, ← Complex.ofReal_log (by linarith : 0 ≤ 1-x^q)]

/-- Exact finite geometric factorization isolates the only logarithmic term. -/
theorem sparse_harmonic_regular_part (q : ℕ) (hq : 0 < q) {x : ℝ}
    (hx : x ∈ Set.Ioo 0 1) :
    sparseHarmonic q (x : ℂ) + (Real.log (1-x) : ℂ)/(q : ℂ) =
      -(Real.log (∑ t ∈ range q, x^t) : ℂ)/(q : ℂ) := by
  have hg : 0 < ∑ t ∈ range q, x^t := by
    have hge : (1 : ℝ) ≤ ∑ t ∈ range q, x^t := by
      calc
        (1 : ℝ) = x^0 := by simp
        _ ≤ ∑ t ∈ range q, x^t :=
          Finset.single_le_sum (fun t _ => pow_nonneg hx.1.le t)
            (Finset.mem_range.mpr hq)
    linarith
  have hlog : Real.log (1-x^q) = Real.log (1-x) + Real.log (∑ t ∈ range q, x^t) := by
    rw [← mul_neg_geom_sum x q,
      Real.log_mul (ne_of_gt (sub_pos.mpr hx.2)) (ne_of_gt hg)]
  rw [sparse_harmonic_real_eq q hq hx, hlog]
  push_cast
  ring

/-- The constant of the finite harmonic remainder is explicit: -log(q)/q. -/
theorem sparse_harmonic_regular_part_tendsto (q : ℕ) (hq : 0 < q) :
    Tendsto (fun x : ℝ =>
      sparseHarmonic q (x : ℂ) + (Real.log (1-x) : ℂ)/(q : ℂ)) (𝓝[<] 1)
      (𝓝 (-(Real.log (q : ℝ) : ℂ)/(q : ℂ))) := by
  have hpoly : Continuous (fun x : ℝ => ∑ t ∈ range q, x^t) := by fun_prop
  have hp : Tendsto (fun x : ℝ => ∑ t ∈ range q, x^t) (𝓝[<] 1) (𝓝 (q : ℝ)) := by
    simpa using (hpoly.tendsto 1).mono_left nhdsWithin_le_nhds
  have hlog : Tendsto (fun x : ℝ => Real.log (∑ t ∈ range q, x^t))
      (𝓝[<] 1) (𝓝 (Real.log (q : ℝ))) :=
    (Real.continuousAt_log (by exact_mod_cast (show q ≠ 0 by omega))).tendsto.comp hp
  have hc := (Complex.continuous_ofReal.tendsto (Real.log (q : ℝ))).comp hlog
  apply (hc.neg.div_const (q : ℂ)).congr'
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ)<1 by norm_num)] with x hx
  exact (sparse_harmonic_regular_part q hq hx).symm

#print axioms FJSparseHarmonic.hasSum_sparse_harmonic
#print axioms FJSparseHarmonic.sparse_harmonic_regular_part
#print axioms FJSparseHarmonic.sparse_harmonic_regular_part_tendsto
end FJSparseHarmonic
