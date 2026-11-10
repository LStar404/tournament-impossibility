import Mathlib
/-! Isolated verified (2026-11-10). Finite exact normalization gates; no asymptotics. -/
set_option autoImplicit false
noncomputable section
namespace NormalizationScalarsCandidate
lemma beta_bounds {n m t k K : ℝ} (hn : 0 < n) (ht : 0 ≤ t)
    (hm : m=n-t) (hk : |k| ≤ K) (hgap : n/2 ≤ m-K) :
    0 < n/(m+k) ∧ n/(m+k) ≤ 2 ∧ |n/(m+k)-1| ≤ 2*(t+K)/n := by
  have hk0 := (abs_nonneg k).trans hk
  have hkl := (abs_le.mp hk).1
  have hden : 0 < m+k := by linarith
  have hlow : n/2 ≤ m+k := by linarith
  refine ⟨div_pos hn hden, (div_le_iff₀ hden).mpr (by linarith), ?_⟩
  have he : n/(m+k)-1=(t-k)/(m+k) := by field_simp [ne_of_gt hden]; linarith
  rw [he, abs_div, abs_of_pos hden]
  have hnum : |t-k| ≤ t+K := by
    calc
      _ ≤ |t|+|k| := abs_sub t k
      _ ≤ t+K := by rw [abs_of_nonneg ht]; exact add_le_add_right hk t
  calc
    _ ≤ (t+K)/(m+k) := div_le_div_of_nonneg_right hnum hden.le
    _ ≤ (t+K)/(n/2) := div_le_div_of_nonneg_left (by linarith) (by linarith) hlow
    _ = _ := by ring
lemma K_budget {n t C δ K : ℝ} (hn : 0 < n) (ht : 0 ≤ t)
    (htn : t ≤ n/2) (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hK : K=4*t*δ+2*(C+1)*t^2/n) :
    0 ≤ K ∧ K/n ≤ 2*δ+(C+1)*t/n := by
  constructor
  · rw [hK]; positivity
  · apply (div_le_iff₀ hn).mpr
    have ht2 : 2*t^2 ≤ n*t := by nlinarith
    have hh := mul_le_mul_of_nonneg_left ht2 (show 0 ≤ C+1 by linarith)
    have hδt : 4*t*δ ≤ 2*n*δ := by nlinarith
    rw [hK]
    apply (le_of_mul_le_mul_right ?_ hn)
    field_simp
    nlinarith
lemma epsilon_budget {n m t C δ K : ℝ} (hn : 0 < n) (ht : 0 ≤ t)
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hK : 0 ≤ K)
    (hgap : n/2 ≤ m-K) (hKb : K/n ≤ 2*δ+(C+1)*t/n) :
    0 ≤ (n*δ+(C+1)*t+K)/(m-K) ∧
    (n*δ+(C+1)*t+K)/(m-K) ≤ 6*δ+4*(C+1)*t/n := by
  have hd : 0 < m-K := by linarith
  have hnum : 0 ≤ n*δ+(C+1)*t+K := by positivity
  have hKu : K ≤ 2*n*δ+(C+1)*t := by
    have h := (div_le_iff₀ hn).mp hKb
    field_simp at h
    nlinarith
  refine ⟨div_nonneg hnum hd.le, ?_⟩
  calc
    _ ≤ (n*δ+(C+1)*t+K)/(n/2) := div_le_div_of_nonneg_left hnum (by linarith) hgap
    _ ≤ (3*n*δ+2*(C+1)*t)/(n/2) := div_le_div_of_nonneg_right (by linarith) (by linarith)
    _ = _ := by field_simp; ring
end NormalizationScalarsCandidate
