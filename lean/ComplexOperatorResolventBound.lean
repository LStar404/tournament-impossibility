import Mathlib

noncomputable section
open scoped InnerProductSpace
namespace ComplexOperatorResolventBound
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def neumann (A : E →L[ℂ] E) (w : ℂ) : E →L[ℂ] E :=
  ∑' k : ℕ, (-(w^2) • (A*A))^k

/-- A genuine operator-norm hypothesis, not a determinant or spectral-radius bound. -/
theorem perturbation_norm (A : E →L[ℂ] E) (w : ℂ) :
    ‖-(w^2) • (A*A)‖ ≤ ‖w‖^2 * ‖A‖^2 := by
  rw [norm_smul, norm_neg, norm_pow, pow_two ‖A‖]
  exact mul_le_mul_of_nonneg_left (norm_mul_le A A) (sq_nonneg ‖w‖)

theorem inverse_and_norm (A : E →L[ℂ] E) (w : ℂ) {q : ℝ}
    (hbound : ‖w‖^2 * ‖A‖^2 ≤ q) (hq : q < 1) :
    (1 + w^2 • (A*A)) * neumann A w = 1 ∧
    neumann A w * (1 + w^2 • (A*A)) = 1 ∧
    ‖neumann A w‖ ≤ 1 / (1-q) := by
  let X : E →L[ℂ] E := -(w^2) • (A*A)
  have hxq : ‖X‖ ≤ q := (perturbation_norm A w).trans hbound
  have hx : ‖X‖ < 1 := hxq.trans_lt hq
  have hn : ‖neumann A w‖ ≤ (1-‖X‖)⁻¹ := by
    have hh := tsum_geometric_le_of_norm_lt_one X hx
    have hid : ‖(1 : E →L[ℂ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    change ‖∑' k : ℕ, X^k‖ ≤ _
    linarith
  refine ⟨?_, ?_, hn.trans ?_⟩
  · simpa [X, neumann, sub_eq_add_neg] using mul_neg_geom_series X hx
  · simpa [X, neumann, sub_eq_add_neg] using geom_series_mul_neg X hx
  · rw [one_div]
    exact inv_anti₀ (sub_pos.mpr hq) (by linarith)

/-- Cauchy--Schwarz source bound for the actual bounded operator inverse. -/
theorem source_bound (A : E →L[ℂ] E) (w : ℂ) {q : ℝ}
    (hbound : ‖w‖^2 * ‖A‖^2 ≤ q) (hq : q < 1) (b : E) :
    ‖⟪b, neumann A w b⟫_ℂ‖ ≤ ‖b‖^2 / (1-q) := by
  have hr := (inverse_and_norm A w hbound hq).2.2
  calc
    _ ≤ ‖b‖ * ‖neumann A w b‖ := norm_inner_le_norm _ _
    _ ≤ ‖b‖ * (‖neumann A w‖ * ‖b‖) :=
      mul_le_mul_of_nonneg_left ((neumann A w).le_opNorm b) (norm_nonneg b)
    _ ≤ ‖b‖ * ((1/(1-q)) * ‖b‖) := by gcongr
    _ = _ := by ring

/-- After the actual linear-energy hypothesis, the quadratic-normalized source
term has an explicit order 1/n bound. The operator-norm hypothesis remains an input. -/
theorem normalized_source_bound (A : E →L[ℂ] E) (w : ℂ) {q K : ℝ}
    (hbound : ‖w‖^2 * ‖A‖^2 ≤ q) (hq : q < 1) (b : E) {n : ℕ}
    (hn : 0 < n) (henergy : ‖b‖^2 ≤ K * (n : ℝ)) :
    ‖⟪b, neumann A w b⟫_ℂ‖ / (n : ℝ)^2 ≤ K / ((n : ℝ)*(1-q)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < 1-q := sub_pos.mpr hq
  calc
    _ ≤ (‖b‖^2 / (1-q)) / (n : ℝ)^2 :=
      div_le_div_of_nonneg_right (source_bound A w hbound hq b) (sq_nonneg _)
    _ ≤ ((K * (n : ℝ)) / (1-q)) / (n : ℝ)^2 := by
      gcongr
    _ = _ := by
      field_simp [ne_of_gt hnpos, ne_of_gt hden]
      <;> ring

end ComplexOperatorResolventBound
#print axioms ComplexOperatorResolventBound.inverse_and_norm
#print axioms ComplexOperatorResolventBound.source_bound

#print axioms ComplexOperatorResolventBound.normalized_source_bound
