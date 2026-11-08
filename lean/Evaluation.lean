import Descent
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Tactic.Ring

namespace NonAlgebraicity
noncomputable section
open scoped BigOperators
open PowerSeries

def seriesTerm (B : PowerSeries ℚ) (z : ℂ) (n : ℕ) : ℂ :=
  ((coeff n B : ℚ) : ℂ) * z ^ n

/-- Absolute convergence together with the value of a rational formal series. -/
def HasSeriesValue (B : PowerSeries ℚ) (z y : ℂ) : Prop :=
  Summable (fun n => ‖seriesTerm B z n‖) ∧ HasSum (seriesTerm B z) y

theorem seriesTerm_mul (B D : PowerSeries ℚ) (z : ℂ) (n : ℕ) :
    seriesTerm (B * D) z n =
      ∑ ij ∈ Finset.antidiagonal n, seriesTerm B z ij.1 * seriesTerm D z ij.2 := by
  simp only [seriesTerm, coeff_mul, Rat.cast_sum, Rat.cast_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have he := Finset.mem_antidiagonal.mp hij
  rw [← he, pow_add]
  ring

theorem HasSeriesValue.mul {B D : PowerSeries ℚ} {z b d : ℂ}
    (hB : HasSeriesValue B z b) (hD : HasSeriesValue D z d) :
    HasSeriesValue (B * D) z (b * d) := by
  constructor
  · simpa only [seriesTerm_mul] using
      summable_norm_sum_mul_antidiagonal_of_summable_norm hB.1 hD.1
  · have hs := (summable_norm_sum_mul_antidiagonal_of_summable_norm hB.1 hD.1).of_norm.hasSum
    have he := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hB.1 hD.1
    rw [hB.2.tsum_eq, hD.2.tsum_eq] at he
    rw [he]
    change HasSum (fun n => seriesTerm (B * D) z n) _
    simpa only [seriesTerm_mul] using hs

theorem hasSeriesValue_X_pow (z : ℂ) (k : ℕ) :
    HasSeriesValue ((X : PowerSeries ℚ) ^ k) z (z ^ k) := by
  have ht : seriesTerm ((X : PowerSeries ℚ) ^ k) z =
      fun n => if n = k then z ^ k else 0 := by
    funext n
    by_cases h : n = k <;> simp [seriesTerm, coeff_X_pow, h]
  rw [HasSeriesValue, ht]
  constructor
  · simpa only [apply_ite, norm_zero] using (hasSum_ite_eq k (‖z ^ k‖)).summable
  · exact hasSum_ite_eq k (z ^ k)

theorem HasSeriesValue.pow {B : PowerSeries ℚ} {z b : ℂ}
    (h : HasSeriesValue B z b) (k : ℕ) : HasSeriesValue (B ^ k) z (b ^ k) := by
  induction k with
  | zero => simpa using hasSeriesValue_X_pow z 0
  | succ k ih => simpa only [pow_succ] using ih.mul h

theorem HasSeriesValue.smul {B : PowerSeries ℚ} {z b : ℂ}
    (h : HasSeriesValue B z b) (c : ℚ) :
    HasSeriesValue (c • B) z ((c : ℂ) * b) := by
  have ht : seriesTerm (c • B) z = fun n => (c : ℂ) * seriesTerm B z n := by
    funext n
    simp [seriesTerm, mul_assoc]
  rw [HasSeriesValue, ht]
  exact ⟨by simpa [norm_mul] using h.1.mul_left ‖(c : ℂ)‖, h.2.mul_left _⟩

/-- Formal zero relations remain zero after absolutely convergent evaluation. -/
theorem relation_evaluates_zero {m n : ℕ} (B : PowerSeries ℚ) (c : Fin m × Fin n → ℚ)
    (hrel : ∑ ij, c ij • ((X : PowerSeries ℚ) ^ ij.1.val * B ^ ij.2.val) = 0)
    {z b : ℂ} (hB : HasSeriesValue B z b) :
    ∑ ij, (c ij : ℂ) * (z ^ ij.1.val * b ^ ij.2.val) = 0 := by
  classical
  have hs := hasSum_sum (s := Finset.univ) (fun ij _ =>
    (((hasSeriesValue_X_pow z ij.1.val).mul (hB.pow ij.2.val)).smul (c ij)).2)
  have ht : (fun k => ∑ ij, seriesTerm (c ij • ((X : PowerSeries ℚ) ^ ij.1.val * B ^ ij.2.val)) z k)
      = fun _ => (0 : ℂ) := by
    funext k
    have hh := congrArg (fun P : PowerSeries ℚ => seriesTerm P z k) hrel
    simpa [seriesTerm, Finset.sum_mul] using hh
  rw [ht] at hs
  exact hs.unique (hasSum_zero)

/-- Convert the rectangular coefficients to Q[Y][X], with outer variable X=z. -/
def arrayPolynomial {m n : ℕ} (c : Fin m × Fin n → ℚ) :
    Polynomial (Polynomial ℚ) :=
  ∑ i, ∑ j, Polynomial.monomial i.val (Polynomial.monomial j.val (c (i,j)))

theorem arrayPolynomial_coeff {m n : ℕ} (c : Fin m × Fin n → ℚ) (i : Fin m) (j : Fin n) :
    ((arrayPolynomial c).coeff i.val).coeff j.val = c (i,j) := by
  classical
  simp [arrayPolynomial, Polynomial.coeff_monomial, ← Fin.ext_iff]

theorem arrayPolynomial_ne_zero {m n : ℕ} (c : Fin m × Fin n → ℚ) (hc : c ≠ 0) :
    arrayPolynomial c ≠ 0 := by
  intro h
  apply hc
  funext ij
  have he := arrayPolynomial_coeff c ij.1 ij.2
  simpa [h] using he.symm

theorem arrayPolynomial_eval {m n : ℕ} (c : Fin m × Fin n → ℚ) (z b : ℂ) :
    (arrayPolynomial c).eval₂ (Polynomial.eval₂RingHom (algebraMap ℚ ℂ) b) z =
      ∑ ij, (c ij : ℂ) * (z ^ ij.1.val * b ^ ij.2.val) := by
  classical
  simp only [arrayPolynomial, Fintype.sum_prod_type, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_monomial]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change ((Polynomial.monomial j.val (c (i,j))).eval₂ (algebraMap ℚ ℂ) b) * z ^ i.val = _
  simp only [Polynomial.eval₂_monomial, eq_ratCast]
  ring

end
end NonAlgebraicity

#print axioms NonAlgebraicity.relation_evaluates_zero
