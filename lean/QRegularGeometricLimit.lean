import QRegularRationalLimit

/-!
# Rational limits along geometric subsequences

This is an isolated extension of the audited 563-module development. It does
not change the earlier full-sequence theorem. The regularity premise is the
existing finite-dimensional **complex** q-kernel definition, not a rational
matrix representation. No transcendence or four-exponentials premise occurs.

Conventions: `q`, `d`, and the subsequence index `e` are natural numbers;
`2 ≤ q`. Thus `q ^ e ≥ 1`, including `q ^ 0 = 1`, so the geometric subsequence
never samples `a 0`. The degree-zero normalization equals one. The full
sequence uses Lean's totalized rational division: its term at `n = 0` is
`a 0` when `d = 0` (because `0 ^ 0 = 1`), and zero when `0 < d`.
That single initial term is immaterial to convergence at `atTop`.
-/

open Filter Topology Polynomial Matrix
open scoped BigOperators
namespace NonAlgebraicity

/-- The quotient normalization is exactly the paper's `q^(-d*e) a(q^e)`.
The exponent on the right is an integer negative of the natural product. -/
theorem geometric_normalization_eq_zpow (q d e : ℕ) (a : ℕ → ℚ) :
    ((a (q ^ e) / ((q ^ e : ℕ) : ℚ)^d : ℚ) : ℂ) =
      (q : ℂ) ^ (-((d * e : ℕ) : ℤ)) * (a (q ^ e) : ℂ) := by
  simp only [Rat.cast_div, Rat.cast_pow, Rat.cast_natCast, Nat.cast_pow]
  simp only [zpow_neg, zpow_natCast, ← pow_mul, div_eq_mul_inv]
  rw [Nat.mul_comm e d, mul_comm]

/-- Rationality requires convergence only on the geometric subsequence.
This proof extracts the matrix-orbit/rational-series argument, accepting its
coefficient limit directly instead of deriving it from a full-sequence limit. -/
theorem qRegular_geometric_scaled_limit_rational (q : ℕ) (hq : 2 ≤ q)
    (a : ℕ → ℚ) (d : ℕ) (L : ℂ)
    (ha : IsQRegular q (fun n => (a n : ℂ)))
    (hlim : Tendsto (fun e => ((a (q ^ e) / ((q ^ e : ℕ) : ℚ)^d : ℚ) : ℂ))
      atTop (𝓝 L)) :
    ∃ r : ℚ, (r : ℂ) = L := by
  obtain ⟨m, M, v, l, he⟩ := qRegular_power_representation q hq _ ha
  let B : PowerSeries ℚ := PowerSeries.mk fun e => a (q ^ e) / ((q ^ e : ℕ) : ℚ)^d
  have hB : PowerSeries.map (algebraMap ℚ ℂ) B =
      PowerSeries.mk (fun e => l ⬝ᵥ (((((q : ℂ)^d)⁻¹ • M)^e) *ᵥ v)) := by
    ext e
    simp only [B, PowerSeries.coeff_map, PowerSeries.coeff_mk]
    change ((a (q ^ e) / ((q ^ e : ℕ) : ℚ)^d : ℚ) : ℂ) = _
    simp only [Rat.cast_div, Rat.cast_pow, Rat.cast_natCast, Nat.cast_pow,
      smul_pow, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    rw [← he]
    simp only [inv_pow, ← pow_mul, Nat.mul_comm e d, div_eq_mul_inv]
    ring
  obtain ⟨P, Q, hQ, hrel⟩ := matrix_output_series_linear_relation (((q : ℂ)^d)⁻¹ • M) v l
  rw [← hB] at hrel
  obtain ⟨p, r, hr, hre⟩ := rational_linear_relation_descends B P Q hQ hrel
  apply rational_limit_of_rational_series B L _ p r hr hre
  simpa [B] using hlim

/-- Theorem A.5's main assertion, with the displayed geometric normalization
and no full-sequence convergence assumption. -/
theorem qRegular_geometric_limit_rational (q : ℕ) (hq : 2 ≤ q)
    (a : ℕ → ℚ) (d : ℕ) (L : ℂ)
    (ha : IsQRegular q (fun n => (a n : ℂ)))
    (hlim : Tendsto (fun e : ℕ =>
      (q : ℂ) ^ (-((d * e : ℕ) : ℤ)) * (a (q ^ e) : ℂ)) atTop (𝓝 L)) :
    ∃ r : ℚ, (r : ℂ) = L := by
  apply qRegular_geometric_scaled_limit_rational q hq a d L ha
  simpa only [geometric_normalization_eq_zpow] using hlim

/-- The previously exported full-sequence endpoint, now obtained as a
corollary of the stronger geometric endpoint by `e ↦ q^e`. Its proposition
is identical to `qRegular_scaled_limit_rational` (with the degree named `d`). -/
theorem qRegular_scaled_limit_rational_from_geometric (q : ℕ) (hq : 2 ≤ q)
    (a : ℕ → ℚ) (d : ℕ) (L : ℂ)
    (ha : IsQRegular q (fun n => (a n : ℂ)))
    (hlim : Tendsto (fun n => ((a n / (n : ℚ)^d : ℚ) : ℂ)) atTop (𝓝 L)) :
    ∃ r : ℚ, (r : ℂ) = L := by
  have hp : Tendsto (fun e : ℕ => q ^ e) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by omega)
  apply qRegular_geometric_scaled_limit_rational q hq a d L ha
  simpa only [Function.comp_def] using hlim.comp hp

/-- The degree-zero geometric endpoint. -/
theorem qRegular_geometric_unscaled_limit_rational (q : ℕ) (hq : 2 ≤ q)
    (a : ℕ → ℚ) (L : ℂ)
    (ha : IsQRegular q (fun n => (a n : ℂ)))
    (hlim : Tendsto (fun e : ℕ => (a (q ^ e) : ℂ)) atTop (𝓝 L)) :
    ∃ r : ℚ, (r : ℂ) = L :=
  qRegular_geometric_scaled_limit_rational q hq a 0 L ha (by simpa using hlim)

/-- Theorem A.5's final sentence: an irrational normalized limit alone
excludes complex q-regularity; no transcendence assumption is needed. -/
theorem not_qRegular_of_scaled_limit_not_rational (q : ℕ) (hq : 2 ≤ q)
    (a : ℕ → ℚ) (d : ℕ) (L : ℂ)
    (hlim : Tendsto (fun n => ((a n / (n : ℚ)^d : ℚ) : ℂ)) atTop (𝓝 L))
    (hL : ¬ ∃ r : ℚ, (r : ℂ) = L) :
    ¬ IsQRegular q (fun n => (a n : ℂ)) := by
  intro ha
  exact hL (qRegular_scaled_limit_rational_from_geometric q hq a d L ha hlim)

end NonAlgebraicity
