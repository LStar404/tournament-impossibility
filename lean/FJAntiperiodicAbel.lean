import Mathlib

/-!
Standalone abstract backend component. Negative Laurent weights of an antiperiodic sequence.
Final evidence: focused/result.json.
The proof uses natural-order partial-sum convergence and Abel's theorem;
it never treats conditional convergence at 1 as unconditional Summable.
-/
noncomputable section
open Filter Topology Finset
namespace FJAntiperiodicAbel

theorem full_period_sum_zero {v : ℕ → ℂ} {b : ℕ}
    (hv : Function.Antiperiodic v b) : (∑ n ∈ range (2*b), v n)=0 := by
  rw [show 2*b=b+b by omega, Finset.sum_range_add]
  have hs : (∑ n ∈ range b, v (b+n)) = -(∑ n ∈ range b, v n) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro n _
    simpa only [Nat.add_comm] using hv n
  rw [hs, add_neg_cancel]

/-- Complete periods cancel exactly; the residual partial period has a
finite norm bound. This is the coefficient fact required by Dirichlet. -/
theorem partial_sums_bounded {v : ℕ → ℂ} {b : ℕ} (hb : 0 < b)
    (hv : Function.Antiperiodic v b) :
    ∀ n, ‖∑ i ∈ range n, v i‖ ≤ ∑ i ∈ range (2*b), ‖v i‖ := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 2*b
    · calc
        ‖∑ i ∈ range n, v i‖ ≤ ∑ i ∈ range n, ‖v i‖ := norm_sum_le _ _
        _ ≤ ∑ i ∈ range (2*b), ‖v i‖ :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
            (fun i _ _ => norm_nonneg (v i))
    · have hbn : 2*b ≤ n := by omega
      have he : (∑ i ∈ range n, v i) = ∑ i ∈ range (n-2*b), v i := by
        calc
          (∑ i ∈ range n, v i) = ∑ i ∈ range (2*b+(n-2*b)), v i := by
            rw [show 2*b+(n-2*b)=n by omega]
          _ = (∑ i ∈ range (2*b), v i) +
              ∑ i ∈ range (n-2*b), v (2*b+i) := Finset.sum_range_add _ _ _
          _ = ∑ i ∈ range (n-2*b), v i := by
            rw [full_period_sum_zero hv, zero_add]
            apply Finset.sum_congr rfl
            intro i _
            simpa only [Nat.add_comm] using hv.periodic_two_mul i
      rw [he]
      exact ih (n-2*b) (by omega)

/-- A generic coefficient-side Dirichlet/Abel bridge. Neither endpoint
convergence nor a function-level remainder estimate is assumed. -/
theorem weighted_abel {v : ℕ → ℂ} {b : ℕ} (hb : 0 < b)
    (hv : Function.Antiperiodic v b) {w : ℕ → ℝ} (hw : Antitone w)
    (hw0 : Tendsto w atTop (𝓝 0)) :
    ∃ ℓ : ℂ, Tendsto
      (fun x : ℝ => ∑' n, ((w n : ℂ)*v n)*(x : ℂ)^n) (𝓝[<] 1) (𝓝 ℓ) := by
  have hC := hw.cauchySeq_series_mul_of_tendsto_zero_of_bounded hw0
    (partial_sums_bounded hb hv)
  obtain ⟨ℓ, hℓ⟩ := cauchySeq_tendsto_of_complete hC
  have hpartials : Tendsto (fun n => ∑ i ∈ range n, (w i : ℂ)*v i)
      atTop (𝓝 ℓ) := by
    simpa only [Complex.real_smul] using hℓ
  have hA := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt hpartials
  rw [tendsto_map'_iff] at hA
  exact ⟨ℓ, hA⟩

theorem inverse_weights_antitone (d : ℕ) :
    Antitone (fun n : ℕ => 1 / ((n+1 : ℕ) : ℝ)^d) := by
  intro m n hmn
  apply one_div_le_one_div_of_le (by positivity)
  apply pow_le_pow_left₀ (by positivity)
  exact_mod_cast Nat.add_le_add_right hmn 1

theorem inverse_weights_tendsto (d : ℕ) (hd : 0 < d) :
    Tendsto (fun n : ℕ => 1 / ((n+1 : ℕ) : ℝ)^d) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hi : Tendsto (fun n : ℕ => (((n+1 : ℕ) : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hn
  simpa only [one_div, inv_pow, zero_pow (by omega : d ≠ 0)] using hi.pow d

/-- Negative Laurent powers, including the conditionally convergent d=1.
Multiplication by x converts this shifted series into the n≥1 series with
powers x^n; the finite endpoint limit is unchanged. -/
theorem inverse_weighted_abel {v : ℕ → ℂ} {b : ℕ} (hb : 0 < b)
    (hv : Function.Antiperiodic v b) (d : ℕ) (hd : 0 < d) :
    ∃ ℓ : ℂ, Tendsto
      (fun x : ℝ => ∑' n, (v (n+1) / ((n+1 : ℕ) : ℂ)^d)*(x : ℂ)^n)
      (𝓝[<] 1) (𝓝 ℓ) := by
  have hv' : Function.Antiperiodic (fun n : ℕ => v (n+1)) b := by
    intro n
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hv (n+1)
  obtain ⟨ℓ, hℓ⟩ := weighted_abel hb hv' (inverse_weights_antitone d)
    (inverse_weights_tendsto d hd)
  refine ⟨ℓ, ?_⟩
  convert hℓ using 1
  ext x
  apply tsum_congr
  intro n
  push_cast
  ring

#print axioms FJAntiperiodicAbel.partial_sums_bounded
#print axioms FJAntiperiodicAbel.weighted_abel
#print axioms FJAntiperiodicAbel.inverse_weighted_abel
end FJAntiperiodicAbel
