import WeightedRecoveryClosure
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Normed.Module.Connected

/-! Termwise analytic differentiation from a genuine coefficient radius >1.
The result concerns the coefficient-tsum evaluation of the same formal series. -/
noncomputable section
open Filter Topology
namespace FormalSeriesDerivativeAtOne
open WeightedCoefficientNorm

def eval (F : PowerSeries ℂ) (z : ℂ) : ℂ := ∑' k, F.coeff k*z^k

def term (F : PowerSeries ℂ) (ell k : ℕ) (z : ℂ) : ℂ :=
  F.coeff k*(k.descFactorial ell : ℂ)*z^(k-ell)

def derivativeSum (F : PowerSeries ℂ) (ell : ℕ) (z : ℂ) : ℂ := ∑' k, term F ell k z

lemma moment_summable {s r : ℝ} (hr : 0 ≤ r) (hrs : r<s)
    (F : PowerSeries ℂ) (hF : Finite s F) (ell : ℕ) :
    Summable (fun k : ℕ => (k : ℝ)^ell*‖F.coeff k‖*r^k) := by
  apply summable_of_sum_le (fun k => by positivity)
    (c := WeightedPolynomialMultiplier.moment (r/s) ell*norm s F)
  intro E
  simpa only [one_pow, one_mul, mul_one] using
    WeightedPolynomialMultiplier.finite_window F E ell r s 1 hr (lt_of_le_of_lt hr hrs)
      (by norm_num) (by simpa using hrs) hF

lemma term_bound (F : PowerSeries ℂ) (ell k : ℕ) {r : ℝ} (hr : 1 ≤ r)
    {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖term F ell k z‖ ≤ (k : ℝ)^ell*‖F.coeff k‖*r^k := by
  have hd : (k.descFactorial ell : ℝ) ≤ (k : ℝ)^ell := by exact_mod_cast Nat.descFactorial_le_pow k ell
  have hp : ‖z‖^(k-ell) ≤ r^k :=
    (pow_le_pow_left₀ (norm_nonneg z) hz _).trans (pow_le_pow_right₀ hr (Nat.sub_le k ell))
  unfold term
  rw [norm_mul, norm_mul, Complex.norm_natCast, norm_pow]
  have h := mul_le_mul (mul_le_mul_of_nonneg_left hd (norm_nonneg (F.coeff k))) hp
    (pow_nonneg (norm_nonneg z) _) (mul_nonneg (norm_nonneg (F.coeff k)) (pow_nonneg (Nat.cast_nonneg k) ell))
  convert h using 1 <;> ring

lemma term_derivative (F : PowerSeries ℂ) (ell k : ℕ) (z : ℂ) :
    HasDerivAt (term F ell k) (term F (ell+1) k z) z := by
  unfold term
  convert (hasDerivAt_pow (k-ell) z).const_mul (F.coeff k*(k.descFactorial ell : ℂ)) using 1
  simp only [Nat.descFactorial_succ, Nat.cast_mul, show k-(ell+1)=k-ell-1 by omega]
  ring

lemma term_summable {s r : ℝ} (hr : 1 ≤ r) (hrs : r<s)
    (F : PowerSeries ℂ) (hF : Finite s F) (ell : ℕ) {z : ℂ} (hz : ‖z‖ ≤ r) :
    Summable (fun k => term F ell k z) := by
  exact ((moment_summable (by linarith) hrs F hF ell).of_nonneg_of_le
    (fun k => norm_nonneg _) (fun k => term_bound F ell k hr hz)).of_norm

lemma derivative_sum {s r : ℝ} (hr : 1 ≤ r) (hrs : r<s)
    (F : PowerSeries ℂ) (hF : Finite s F) (ell : ℕ) {z : ℂ}
    (hz : z∈Metric.ball (0 : ℂ) r) :
    HasDerivAt (derivativeSum F ell) (derivativeSum F (ell+1) z) z := by
  change HasDerivAt (fun y => ∑' k, term F ell k y) (∑' k, term F (ell+1) k z) z
  apply hasDerivAt_tsum_of_isPreconnected (t := Metric.ball (0 : ℂ) r) (y₀ := (0 : ℂ))
    (moment_summable (by linarith) hrs F hF (ell+1)) Metric.isOpen_ball Metric.isPreconnected_ball
  · intro k y hy
    exact term_derivative F ell k y
  · intro k y hy
    have hy' : ‖y‖<r := by simpa only [Metric.mem_ball, dist_zero_right] using hy
    exact term_bound F (ell+1) k hr hy'.le
  · simp only [Metric.mem_ball, dist_self]
    linarith
  · exact term_summable hr hrs F hF ell (by simpa using (show (0 : ℝ) ≤ r by linarith))
  · exact hz

lemma iterated_derivative {s r : ℝ} (hr : 1 ≤ r) (hrs : r<s)
    (F : PowerSeries ℂ) (hF : Finite s F) (ell : ℕ) :
    ∀ z∈Metric.ball (0 : ℂ) r, iteratedDeriv ell (eval F) z=derivativeSum F ell z := by
  induction ell with
  | zero => intro z hz; simp [iteratedDeriv_zero, derivativeSum, term, eval]
  | succ ell ih =>
    intro z hz
    have he : iteratedDeriv ell (eval F) =ᶠ[𝓝 z] derivativeSum F ell := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hz] with y hy
      exact ih y hy
    rw [iteratedDeriv_succ, he.deriv_eq]
    exact (derivative_sum hr hrs F hF ell hz).deriv

/-- The radius premise is essential: unit-radius coefficient moments alone do
not supply a neighborhood of the boundary point 1. -/
theorem at_one {s : ℝ} (hs : 1<s) (F : PowerSeries ℂ) (hF : Finite s F) (ell : ℕ) :
    iteratedDeriv ell (eval F) 1=
      WeightedRecoveryClosure.fallingFactorialSum (fun k => F.coeff k) ell := by
  have hr : (1 : ℝ) ≤ (1+s)/2 := by linarith
  have hrs : (1+s)/2<s := by linarith
  have hz : (1 : ℂ)∈Metric.ball 0 ((1+s)/2) := by
    have hone : ‖(1 : ℂ)‖=1 := by norm_num
    simp only [Metric.mem_ball, dist_zero_right, hone]
    linarith
  rw [iterated_derivative hr hrs F hF ell 1 hz]
  unfold derivativeSum WeightedRecoveryClosure.fallingFactorialSum
  apply tsum_congr
  intro k
  simp [term, mul_comm]

lemma polynomial_finite (P : Polynomial ℂ) {s : ℝ} (hs : 0 ≤ s) : Finite s (P : PowerSeries ℂ) := by
  apply summable_of_sum_le (nonneg hs _)
    (c := ∑ k∈P.support, mass s (P : PowerSeries ℂ) k)
  intro E
  apply WeightedRecoveryClosure.sum_restrict E P.support _ (nonneg hs _)
  intro k hk hnot
  have hz : P.coeff k=0 := by simpa only [Polynomial.mem_support_iff, not_not] using hnot
  simp [mass, Polynomial.coeff_coe, hz]

lemma polynomial_eval (P : Polynomial ℂ) : eval (P : PowerSeries ℂ)=P.eval := by
  funext z
  unfold eval
  simp only [Polynomial.coeff_coe]
  rw [tsum_eq_sum (s := P.support)]
  · exact (Polynomial.eval_eq_sum).symm
  · intro k hk
    have hz : P.coeff k=0 := by simpa only [Polynomial.mem_support_iff, not_not] using hk
    rw [hz, zero_mul]

theorem polynomial_at_one (P : Polynomial ℂ) (ell : ℕ) :
    iteratedDeriv ell P.eval 1=WeightedRecoveryClosure.fallingFactorialSum P.coeff ell := by
  have h := at_one (by norm_num : (1 : ℝ)<17/16) (P : PowerSeries ℂ)
    (polynomial_finite P (by norm_num)) ell
  simpa only [polynomial_eval, Polynomial.coeff_coe] using h
end FormalSeriesDerivativeAtOne
#print axioms FormalSeriesDerivativeAtOne.at_one
#print axioms FormalSeriesDerivativeAtOne.polynomial_at_one
