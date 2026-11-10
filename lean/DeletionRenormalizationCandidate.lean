import IndependentDeletionMass

/-! Verified in the 557-module direct-Lean compilation and declaration audit.
Finite mass, density and marginal algebra only; no spectral or scaling claim. -/
set_option autoImplicit false
noncomputable section
namespace DeletionRenormalizationCandidate
open Finset

lemma denominator_pos {m k K : ℝ} (hK : |k| ≤ K) (hm : K < m) :
    0 < m+k := by
  have hk := (abs_le.mp hK).1
  linarith

lemma normalized_mass {m k x : ℝ} (hm : 0 < m) (hk : 0 < m+k)
    (hx : x=m+k) : m/(m+k)*x=m := by
  rw [hx]
  exact div_mul_cancel₀ _ (ne_of_gt hk)

lemma density_bound {n m k K C a : ℝ} (hn : 0 < n)
    (hK : |k| ≤ K) (hm : K < m) (ha : a ≤ C/n) (hC : 0 ≤ C) :
    n/(m+k)*a ≤ C/(m-K) := by
  have hd := denominator_pos hK hm
  have hdK : 0 < m-K := sub_pos.mpr hm
  have hlow : m-K ≤ m+k := by have hh := (abs_le.mp hK).1; linarith
  calc
    n/(m+k)*a ≤ n/(m+k)*(C/n) :=
      mul_le_mul_of_nonneg_left ha (div_nonneg hn.le hd.le)
    _ = C/(m+k) := by field_simp <;> ring
    _ ≤ C/(m-K) := div_le_div_of_nonneg_left hC hdK hlow

/-- Exact marginal formula, with d the removed row or column mass. -/
lemma marginal_exact {n m t k r d : ℝ} (hm : m=n-t) (hd : m+k ≠ 0) :
    n/(m+k)*(1+r-d)-1 = (n*r-n*d+t-k)/(m+k) := by
  field_simp
  nlinarith

lemma marginal_bound {n m t k K C δ r d : ℝ}
    (hn : 0 < n) (ht : 0 ≤ t) (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hm : m=n-t) (hK : |k| ≤ K) (hsmall : K < m)
    (hr : |r| ≤ δ) (hd0 : 0 ≤ d) (hd : d ≤ C*t/n) :
    |n/(m+k)*(1+r-d)-1| ≤ (n*δ+(C+1)*t+K)/(m-K) := by
  have hden := denominator_pos hK hsmall
  have hdenK : 0 < m-K := sub_pos.mpr hsmall
  have hlow : m-K ≤ m+k := by have hh := (abs_le.mp hK).1; linarith
  have hK0 : 0 ≤ K := (abs_nonneg k).trans hK
  have hnd : n*d ≤ C*t := by
    have hh := (le_div_iff₀ hn).mp hd
    nlinarith
  have hnum : |n*r-n*d+t-k| ≤ n*δ+(C+1)*t+K := by
    apply abs_le.mpr
    have hr' := abs_le.mp hr
    have hk' := abs_le.mp hK
    have hnr1 := mul_le_mul_of_nonneg_left hr'.1 hn.le
    have hnr2 := mul_le_mul_of_nonneg_left hr'.2 hn.le
    have hnd0 := mul_nonneg hn.le hd0
    constructor <;> nlinarith
  rw [marginal_exact hm (ne_of_gt hden), abs_div, abs_of_pos hden]
  exact (div_le_div_of_nonneg_right hnum hden.le).trans
    (div_le_div_of_nonneg_left (by positivity) hdenK hlow)

/-- Actual finite retained mass after independent deletion. -/
def retainedScale {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (I J : Finset (Fin n)) (m k : ℝ) : ℝ :=
  (n:ℝ)/(m+k)*IndependentDeletionMass.remainingMass A I J

theorem retainedScale_mass {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (I J : Finset (Fin n)) {m k : ℝ}
    (hm : m=(n:ℝ)-I.card) (hm0 : 0 < m) (hk0 : 0 < m+k)
    (hk : k=IndependentDeletionMass.deletionExcess A I J) :
    retainedScale A I J m k=m := by
  have he : k=(n:ℝ)/m*IndependentDeletionMass.remainingMass A I J-m := by
    simpa [IndependentDeletionMass.deletionExcess, ← hm] using hk
  unfold retainedScale
  field_simp [ne_of_gt hm0] at he
  field_simp [ne_of_gt hk0]
  nlinarith

end DeletionRenormalizationCandidate
