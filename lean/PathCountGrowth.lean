import Application
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Tactic

/-!
A growth obstruction for the actual extremal path counts.  The only combinatorial
input is the explicitly parameterized asymptotic statement; no assertion about
finite-dimensional representations is included as an assumption here.
-/
open Filter Topology

namespace NonAlgebraicity

lemma normalizedCoefficient_real_nonneg (n : ℕ) :
    0 ≤ (normalizedCoefficient n : ℝ) := by
  unfold normalizedCoefficient
  split_ifs <;> positivity

lemma normalizedCoefficient_real_le (n : ℕ) :
    (normalizedCoefficient n : ℝ) ≤
      (2 : ℝ)^n * (maximalPathCount n : ℝ) / (n.factorial : ℝ) := by
  by_cases hn : n = 0
  · subst n
    simp only [normalizedCoefficient_zero, Rat.cast_zero, pow_zero,
      Nat.factorial_zero, Nat.cast_one, div_one, one_mul]
    positivity
  · have hp : (2 : ℝ)^(n - 1) ≤ (2 : ℝ)^n :=
      pow_le_pow_right₀ (by norm_num) (Nat.sub_le n 1)
    simp only [normalizedCoefficient, ite_eq_right hn, Rat.cast_div,
      Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_natCast]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg _)) (Nat.cast_nonneg _)

/-- An exponential bound on `P(n)` forces its factorial normalization to vanish. -/
theorem normalizedCoefficient_tendsto_zero_of_exponential_bound
    (C D : ℝ) (_hC : 0 ≤ C) (_hD : 0 ≤ D)
    (hbound : ∀ n, (maximalPathCount n : ℝ) ≤ C * D^n) :
    Tendsto (fun n => (normalizedCoefficient n : ℂ)) atTop (𝓝 0) := by
  have hupper : Tendsto (fun n => C * ((2 * D)^n / (n.factorial : ℝ)))
      atTop (𝓝 0) := by
    simpa using (FloorSemiring.tendsto_pow_div_factorial_atTop (2 * D)).const_mul C
  have hr : Tendsto (fun n => (normalizedCoefficient n : ℝ)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    · exact normalizedCoefficient_real_nonneg
    · intro n
      calc
        (normalizedCoefficient n : ℝ) ≤
            (2 : ℝ)^n * (maximalPathCount n : ℝ) / (n.factorial : ℝ) :=
          normalizedCoefficient_real_le n
        _ ≤ (2 : ℝ)^n * (C * D^n) / (n.factorial : ℝ) :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hbound n) (by positivity)) (by positivity)
        _ = C * ((2 * D)^n / (n.factorial : ℝ)) := by rw [mul_pow]; ring
  have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp hr
  convert hc using 1
  rfl

/-- Conditional on the stated nonzero limit, actual maximal counts have no
uniform exponential upper bound, hence in particular no polynomial bound. -/
theorem maximalPathCount_not_exponentially_bounded
    (h : ExtremalAsymptotic) :
    ¬ ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      ∀ n, (maximalPathCount n : ℝ) ≤ C * D^n := by
  rintro ⟨C, D, hC, hD, hb⟩
  have hne : extremalConstant ≠ 0 := by
    apply div_ne_zero _ cos_one_ne_zero
    have hc : (Real.cosh (1 : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.cosh_pos 1))
    simpa only [Complex.ofReal_cosh, Complex.ofReal_one] using hc
  exact hne (tendsto_nhds_unique h
    (normalizedCoefficient_tendsto_zero_of_exponential_bound C D hC hD hb))

/-- A shrinking-index recursion with uniformly bounded linear steps has at
most exponential growth. This deliberately uses a coarse bound rather than
requiring logarithmic digit-length estimates. -/
theorem digit_recursion_exponential_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (q : ℕ) (hq : 2 ≤ q) (A : Fin q → E →L[ℂ] E)
    (V : ℕ → E)
    (hV : ∀ n, n ≠ 0 → V n = A ⟨n % q, Nat.mod_lt n (by omega)⟩ (V (n / q))) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n, ‖V n‖ ≤ ‖V 0‖ * D^n := by
  classical
  let D : ℝ := 1 + ∑ j : Fin q, ‖A j‖
  have hD : 1 ≤ D := by
    have hs : 0 ≤ ∑ j : Fin q, ‖A j‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    dsimp [D]
    linarith
  have hA (j : Fin q) : ‖A j‖ ≤ D := by
    have hj : ‖A j‖ ≤ ∑ k : Fin q, ‖A k‖ :=
      Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
    dsimp [D]
    linarith
  refine ⟨D, le_trans zero_le_one hD, ?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n; simp
    · have hsmall : n / q < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) hq
      rw [hV n hn]
      calc
        ‖A ⟨n % q, Nat.mod_lt n (by omega)⟩ (V (n / q))‖ ≤
            ‖A ⟨n % q, Nat.mod_lt n (by omega)⟩‖ * ‖V (n / q)‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ ≤ D * (‖V 0‖ * D^(n / q)) :=
          mul_le_mul (hA _) (ih _ hsmall) (norm_nonneg _) (le_trans zero_le_one hD)
        _ = ‖V 0‖ * D^(n / q + 1) := by rw [pow_succ]; ring
        _ ≤ ‖V 0‖ * D^n := mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hD (by omega)) (norm_nonneg _)

/-- Actual path counts admit no fixed finite alphabet of continuous-linear
 digit transitions. In particular this applies to fixed finite-dimensional
 complex matrix representations. -/
theorem maximalPathCount_no_linear_digit_representation
    (h : ExtremalAsymptotic)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (q : ℕ) (hq : 2 ≤ q) (A : Fin q → E →L[ℂ] E)
    (V : ℕ → E) (f : E →L[ℂ] ℂ)
    (hV : ∀ n, n ≠ 0 → V n = A ⟨n % q, Nat.mod_lt n (by omega)⟩ (V (n / q)))
    (hout : ∀ n, (maximalPathCount n : ℂ) = f (V n)) : False := by
  obtain ⟨D, hD, hb⟩ := digit_recursion_exponential_bound q hq A V hV
  apply maximalPathCount_not_exponentially_bounded h
  refine ⟨‖f‖ * ‖V 0‖, D, mul_nonneg (norm_nonneg _) (norm_nonneg _), hD, ?_⟩
  intro n
  calc
    (maximalPathCount n : ℝ) = ‖(maximalPathCount n : ℂ)‖ := by simp
    _ = ‖f (V n)‖ := by rw [hout n]
    _ ≤ ‖f‖ * ‖V n‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖f‖ * (‖V 0‖ * D^n) := mul_le_mul_of_nonneg_left (hb n) (norm_nonneg _)
    _ = (‖f‖ * ‖V 0‖) * D^n := by ring

#print axioms digit_recursion_exponential_bound
#print axioms maximalPathCount_no_linear_digit_representation
#print axioms maximalPathCount_not_exponentially_bounded
end NonAlgebraicity
