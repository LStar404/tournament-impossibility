import PermanentCircleEnvelope
import PermanentCirclePolynomialDecay

/-! Uncompiled integration candidate. The polynomial below is the literal
finite permanent of P + X M, not a core or formal Gaussian proxy. -/
noncomputable section
namespace PermanentActualCircleTail
open PermanentSpectralFrame PermanentPolynomialCircleTail

/-- Explicit constant independent of n and of the matrix within the specified
entry/score/operator class. No optimization of this constant is intended. -/
def tailConstant (K C R q δ : ℝ) (p : ℕ) : ℝ :=
  R/(R-1) *
    (Real.exp (2*R*K + Real.log R + ((1+R*C)/(1-R*q))^2 / (2*(δ*Real.log R))) *
      (p.factorial : ℝ) / ((δ*Real.log R)/2)^p)

lemma tailConstant_nonneg {K C R q δ : ℝ} (hR : 1 < R) (hδ : 0 < δ) (p : ℕ) :
    0 ≤ tailConstant K C R q δ p := by
  unfold tailConstant
  have hl : 0 < Real.log R := Real.log_pos hR
  have hRm : 0 < R-1 := sub_pos.mpr hR
  have hRp : 0 < R := zero_lt_one.trans hR
  positivity

/-- True permanent-polynomial tail at every linear cutoff and every fixed order.
The circle envelope is proved from the matrix hypotheses rather than assumed. -/
theorem actual_tail_bound {n : ℕ} (hn : 0 < n)
    (M : Matrix (Fin n) (Fin n) ℂ) {K C R q δ : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hR : 1 < R) (hq : 0 ≤ q) (hδ : 0 < δ)
    (hrow : ∀ i, ‖∑ j, M i j‖ ≤ K/n)
    (hcol : ∀ j, ‖∑ i, M i j‖ ≤ K/n)
    (hentry : ∀ i j, ‖M i j‖ ≤ C/n)
    (hM : ‖Matrix.toEuclideanCLM (𝕜:=ℂ) M‖ ≤ q) (hRq : R*q < 1) (p : ℕ) :
    (∑ k ∈ (permanentPolynomial (averaging n) M).support.filter
      (fun k => ⌊δ*(n : ℝ)⌋₊ < k),
      ‖(permanentPolynomial (averaging n) M).coeff k‖) ≤
      ((n.factorial : ℝ)/(n : ℝ)^n) * tailConstant K C R q δ p / (n : ℝ)^p := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hRp : 0 ≤ R := (zero_lt_one.trans hR).le
  have hD : 0 ≤ (n.factorial : ℝ)/(n : ℝ)^n := by positivity
  have hcircle : ∀ z : ℂ, ‖z‖ = R →
      ‖Matrix.permanent (averaging n+z • M)‖ ≤
        ((n.factorial : ℝ)/(n : ℝ)^n) *
        Real.exp (2*R*K+((1+R*C)/(1-R*q))*Real.sqrt (n : ℝ)) := by
    intro z hz
    have h := actual_permanent_circle_envelope hn M z hK hC hRp hq
      hrow hcol hentry hz.le hM hRq
    have he : 2*R*K+((1+R*C)/(1-R*q))*Real.sqrt (n : ℝ) =
        2*R*K+(1+R*C)*Real.sqrt (n : ℝ)/(1-R*q) := by ring
    rw [he]
    exact h
  have h := PermanentCirclePolynomialDecay.actual_permanent_floor_tail
    (averaging n) M (2*R*K) ((1+R*C)/(1-R*q)) hR hδ hD hn p hcircle
  convert h using 1 <;> dsimp [tailConstant] <;> ring

/-- Normalization agrees with the permanent of J/n, namely n!/n^n.
The coefficient tail belongs to the actual polynomial, including all degrees. -/
theorem normalized_actual_tail_bound {n : ℕ} (hn : 0 < n)
    (M : Matrix (Fin n) (Fin n) ℂ) {K C R q δ : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hR : 1 < R) (hq : 0 ≤ q) (hδ : 0 < δ)
    (hrow : ∀ i, ‖∑ j, M i j‖ ≤ K/n)
    (hcol : ∀ j, ‖∑ i, M i j‖ ≤ K/n)
    (hentry : ∀ i j, ‖M i j‖ ≤ C/n)
    (hM : ‖Matrix.toEuclideanCLM (𝕜:=ℂ) M‖ ≤ q) (hRq : R*q < 1) (p : ℕ) :
    (∑ k ∈ (permanentPolynomial (averaging n) M).support.filter
      (fun k => ⌊δ*(n : ℝ)⌋₊ < k),
      ‖(permanentPolynomial (averaging n) M).coeff k‖) /
        ((n.factorial : ℝ)/(n : ℝ)^n) ≤ tailConstant K C R q δ p / (n : ℝ)^p := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hD : 0 < (n.factorial : ℝ)/(n : ℝ)^n := by positivity
  apply (div_le_iff₀ hD).mpr
  have h := actual_tail_bound hn M hK hC hR hq hδ hrow hcol hentry hM hRq p
  convert h using 1 <;> ring

/-- Convenient specialization for the already derived q=3/4 graph bound.
The radius 5/4 remains strictly outside the evaluation circle. -/
theorem normalized_actual_tail_three_quarters {n : ℕ} (hn : 0 < n)
    (M : Matrix (Fin n) (Fin n) ℂ) {K C δ : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hδ : 0 < δ)
    (hrow : ∀ i, ‖∑ j, M i j‖ ≤ K/n)
    (hcol : ∀ j, ‖∑ i, M i j‖ ≤ K/n)
    (hentry : ∀ i j, ‖M i j‖ ≤ C/n)
    (hM : ‖Matrix.toEuclideanCLM (𝕜:=ℂ) M‖ ≤ 3/4) (p : ℕ) :
    (∑ k ∈ (permanentPolynomial (averaging n) M).support.filter
      (fun k => ⌊δ*(n : ℝ)⌋₊ < k),
      ‖(permanentPolynomial (averaging n) M).coeff k‖) /
        ((n.factorial : ℝ)/(n : ℝ)^n) ≤
      tailConstant K C (5/4) (3/4) δ p / (n : ℝ)^p := by
  exact normalized_actual_tail_bound hn M hK hC (by norm_num) (by norm_num)
    hδ hrow hcol hentry hM (by norm_num) p

end PermanentActualCircleTail
#print axioms PermanentActualCircleTail.actual_tail_bound
#print axioms PermanentActualCircleTail.normalized_actual_tail_bound
#print axioms PermanentActualCircleTail.normalized_actual_tail_three_quarters
