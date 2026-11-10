import BalancedHessianInverse

/-! Verified in the 557-module direct-Lean compilation and declaration audit.
The centering bridge below uses real matrices. The last section supplies
literal finite Hessian and gauge identities, independent of spectral input. -/
set_option autoImplicit false
noncomputable section
namespace ActualHessianFinite
open Matrix Finset
variable {m : ℕ}
abbrev I (m : ℕ) := Fin m
abbrev Block (m : ℕ) := Fin m ⊕ Fin m

def row (M : Matrix (I m) (I m) ℝ) (i : I m) := ∑ j, M i j
def col (M : Matrix (I m) (I m) ℝ) (j : I m) := ∑ i, M i j
def r (M : Matrix (I m) (I m) ℝ) (i : I m) := row M i - 1
def c (M : Matrix (I m) (I m) ℝ) (j : I m) := col M j - 1
def mu (M : Matrix (I m) (I m) ℝ) := (∑ i, r M i) / (m : ℝ)
def P (m : ℕ) : Matrix (I m) (I m) ℝ := fun _ _ => 1 / (m : ℝ)
def correction (M : Matrix (I m) (I m) ℝ) : Matrix (I m) (I m) ℝ :=
  fun i j => (r M i + c M j - mu M) / (m : ℝ)
def centered (M : Matrix (I m) (I m) ℝ) := M - P m - correction M

theorem sum_residuals (M : Matrix (I m) (I m) ℝ) :
    ∑ i, r M i = ∑ j, c M j := by
  simp only [r, c, row, col, Finset.sum_sub_distrib]
  rw [Finset.sum_comm]

theorem sum_r (hm : 0 < m) (M : Matrix (I m) (I m) ℝ) :
    ∑ i, r M i = (m : ℝ) * mu M := by
  have hn : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  unfold mu
  field_simp

theorem sum_c (hm : 0 < m) (M : Matrix (I m) (I m) ℝ) :
    ∑ j, c M j = (m : ℝ) * mu M := by
  rw [← sum_residuals, sum_r hm]

theorem decomposition (M : Matrix (I m) (I m) ℝ) :
    M = centered M + P m + correction M := by
  unfold centered
  abel

theorem correction_row (hm : 0 < m) (M : Matrix (I m) (I m) ℝ) (i : I m) :
    ∑ j, correction M i j = r M i := by
  have hn : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  simp only [correction, ← Finset.sum_div, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [sum_c hm]
  field_simp
  <;> ring

theorem correction_col (hm : 0 < m) (M : Matrix (I m) (I m) ℝ) (j : I m) :
    ∑ i, correction M i j = c M j := by
  have hn : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  simp only [correction, ← Finset.sum_div, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [sum_r hm]
  field_simp
  <;> ring

theorem centered_row (hm : 0 < m) (M : Matrix (I m) (I m) ℝ) (i : I m) :
    ∑ j, centered M i j = 0 := by
  have hn : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  simp only [centered, Matrix.sub_apply, Finset.sum_sub_distrib]
  rw [correction_row hm]
  simp [P, r, row, hn]

theorem centered_col (hm : 0 < m) (M : Matrix (I m) (I m) ℝ) (j : I m) :
    ∑ i, centered M i j = 0 := by
  have hn : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  simp only [centered, Matrix.sub_apply, Finset.sum_sub_distrib]
  rw [correction_col hm]
  simp [P, c, col, hn]

/-- This equality makes the explicit residual centering genuine Π M Π. -/
theorem centered_projection (hm : 0 < m) (M : Matrix (I m) (I m) ℝ) :
    centered M = (1 - P m) * M * (1 - P m) := by
  have hn : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hp : P m * P m = P m := by
    ext i j
    simp [Matrix.mul_apply, P, hn]
  have hbL : P m * centered M = 0 := by
    ext i j
    simp only [Matrix.mul_apply, P, ← Finset.mul_sum]
    rw [centered_col hm]
    simp
  have hbR : centered M * P m = 0 := by
    ext i j
    simp only [Matrix.mul_apply, P, ← Finset.sum_mul]
    rw [centered_row hm]
    simp
  let L : Matrix (I m) (I m) ℝ := fun i _ => (r M i-mu M)/(m : ℝ)
  have hL : (1-P m)*correction M = L := by
    rw [Matrix.sub_mul, Matrix.one_mul]
    ext i j
    simp only [Matrix.sub_apply, Matrix.mul_apply, P, ← Finset.mul_sum]
    rw [correction_col hm]
    dsimp [correction, L]
    field_simp
    <;> ring
  have hD : (1 - P m) * correction M * (1 - P m) = 0 := by
    rw [hL, Matrix.mul_sub, Matrix.mul_one]
    ext i j
    change (r M i-mu M)/(m : ℝ) - (∑ _k : I m, ((r M i-mu M)/(m : ℝ))*(1/(m : ℝ))) = 0
    simp [hn]
    <;> field_simp
    <;> ring
  conv_rhs => rw [decomposition M]
  simp only [Matrix.mul_add, Matrix.add_mul]
  have hP : (1 - P m) * P m * (1 - P m) = 0 := by
    simp [Matrix.sub_mul, hp]
  rw [hD, hP]
  simp [Matrix.sub_mul, Matrix.mul_sub, hbL, hbR]

theorem mu_bound (hm : 0 < m) (M : Matrix (I m) (I m) ℝ) {ε : ℝ}
    (hr : ∀ i, |r M i| ≤ ε) : |mu M| ≤ ε := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsum : |∑ i, r M i| ≤ (m : ℝ) * ε := by
    calc
      _ ≤ ∑ i, |r M i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : I m, ε := Finset.sum_le_sum (fun i _ => hr i)
      _ = _ := by simp
  simpa [mu, abs_div, abs_of_pos hmR] using
    (div_le_iff₀ hmR).mpr (by simpa [mul_comm] using hsum)

theorem correction_bound (hm : 0 < m) (M : Matrix (I m) (I m) ℝ) {ε : ℝ}
    (hr : ∀ i, |r M i| ≤ ε) (hc : ∀ j, |c M j| ≤ ε) (i j : I m) :
    |correction M i j| ≤ 3 * ε / (m : ℝ) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hμ := mu_bound hm M hr
  have hh : |r M i + c M j - mu M| ≤ 3 * ε := by
    calc
      _ ≤ |r M i + c M j| + |mu M| := abs_sub _ _
      _ ≤ (|r M i| + |c M j|) + |mu M| := add_le_add (abs_add_le _ _) le_rfl
      _ ≤ 3 * ε := by linarith [hr i, hc j]
  simpa [correction, abs_div, abs_of_pos hmR] using div_le_div_of_nonneg_right hh hmR.le

theorem centered_density (hm : 0 < m) (M : Matrix (I m) (I m) ℝ) {C ε : ℝ}
    (hM : ∀ i j, 0 ≤ M i j) (hd : ∀ i j, M i j ≤ C / (m : ℝ))
    (hε : ε ≤ 1) (hr : ∀ i, |r M i| ≤ ε) (hc : ∀ j, |c M j| ≤ ε)
    (i j : I m) : |centered M i j| ≤ (C + 4) / (m : ℝ) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hD := correction_bound hm M hr hc i j
  calc
    _ ≤ |M i j| + |P m i j| + |correction M i j| := by
      exact (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ C / (m : ℝ) + 1 / (m : ℝ) + 3 * ε / (m : ℝ) := by
      apply add_le_add
      · exact add_le_add (by simpa [abs_of_nonneg (hM i j)] using hd i j)
          (by simp [P, abs_of_nonneg hmR.le])
      · exact hD
    _ ≤ (C + 4) / (m : ℝ) := by
      apply (le_div_iff₀ hmR).2
      field_simp
      nlinarith

def actual (M : Matrix (I m) (I m) ℝ) : Matrix (Block m) (Block m) ℝ :=
  Matrix.fromBlocks (Matrix.diagonal (row M)) M M.transpose (Matrix.diagonal (col M))
def model (M : Matrix (I m) (I m) ℝ) : Matrix (Block m) (Block m) ℝ :=
  Matrix.fromBlocks 1 (centered M + P m) (centered M + P m).transpose 1
def perturbation (M : Matrix (I m) (I m) ℝ) : Matrix (Block m) (Block m) ℝ :=
  Matrix.fromBlocks (Matrix.diagonal (r M)) (correction M)
    (correction M).transpose (Matrix.diagonal (c M))
def sign : Block m → ℝ := Sum.elim (fun _ => 1) (fun _ => -1)
def gauge (m : ℕ) : Matrix (Block m) (Block m) ℝ :=
  fun i j => (2 * (m : ℝ))⁻¹ * sign i * sign j

theorem actual_eq_model_add (M : Matrix (I m) (I m) ℝ) :
    actual M = model M + perturbation M := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  all_goals simp [actual, model, perturbation, centered, r, c,
    Matrix.diagonal_apply, Matrix.one_apply, Matrix.transpose_apply]
  all_goals (try split_ifs) <;> ring

theorem perturbation_row_bound (hm : 0 < m) (M : Matrix (I m) (I m) ℝ)
    {ε : ℝ} (hr : ∀ i, |r M i| ≤ ε) (hc : ∀ j, |c M j| ≤ ε)
    (i : Block m) : (∑ j, |perturbation M i j|) ≤ 4 * ε := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hn := ne_of_gt hmR
  have hbR (i : I m) : (∑ j, |correction M i j|) ≤ 3 * ε := by
    calc
      _ ≤ ∑ _j : I m, 3 * ε / (m : ℝ) :=
        Finset.sum_le_sum (fun j _ => correction_bound hm M hr hc i j)
      _ = _ := by simp; field_simp
  have hbC (j : I m) : (∑ i, |correction M i j|) ≤ 3 * ε := by
    calc
      _ ≤ ∑ _i : I m, 3 * ε / (m : ℝ) :=
        Finset.sum_le_sum (fun i _ => correction_bound hm M hr hc i j)
      _ = _ := by simp; field_simp
  rcases i with i | i
  · simp only [Fintype.sum_sum_type, perturbation, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂]
    simp only [Matrix.diagonal_apply, apply_ite abs, abs_zero]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    linarith [hr i, hbR i]
  · simp only [Fintype.sum_sum_type, perturbation, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.transpose_apply]
    simp only [Matrix.diagonal_apply, apply_ite abs, abs_zero]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    linarith [hc i, hbC i]

/-- The actual Hessian's gauge kernel is exact even before any smallness input. -/
theorem actual_sign (M : Matrix (I m) (I m) ℝ) : actual M *ᵥ sign = 0 := by
  funext i
  rcases i with i | i
  all_goals simp [Matrix.mulVec, dotProduct, actual, sign,
    Fintype.sum_sum_type, Matrix.diagonal_apply, row, col]

theorem gauge_actual (M : Matrix (I m) (I m) ℝ) : gauge m * actual M = 0 := by
  ext i j
  rcases j with j | j
  all_goals simp [Matrix.mul_apply, gauge, actual, sign,
    Fintype.sum_sum_type, Matrix.diagonal_apply, row, col,
    Finset.mul_sum, Finset.sum_mul]
  all_goals ring

theorem gauge_perturbation (hm : 0 < m) (M : Matrix (I m) (I m) ℝ) :
    gauge m * perturbation M = 0 := by
  ext i j
  rcases j with j | j
  all_goals simp only [Matrix.mul_apply, Fintype.sum_sum_type, perturbation,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.transpose_apply]
  all_goals simp [gauge, sign, Matrix.diagonal_apply, ← Finset.mul_sum,
    correction_row hm, correction_col hm]

end ActualHessianFinite
#print axioms ActualHessianFinite.centered_projection
#print axioms ActualHessianFinite.perturbation_row_bound
#print axioms ActualHessianFinite.gauge_perturbation
