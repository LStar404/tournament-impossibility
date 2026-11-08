import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
The exact transcendence-theory input used in Appendix A.1 is named explicitly.
The installed mathlib contains the analytic part of Lindemann--Weierstrass,
but not the complete theorem. No axiom is introduced here.
-/
namespace NonAlgebraicity

noncomputable def extremalConstant : ℂ := Complex.cosh 1 / Complex.cos 1

def FourExponentialIndependence : Prop :=
  ∀ c : Fin 4 → ℂ, (∀ j, IsAlgebraic ℚ (c j)) →
    (∑ j : Fin 4, c j * Complex.exp (![1, -1, Complex.I, -Complex.I] j)) = 0 →
    ∀ j, c j = 0

theorem cos_one_ne_zero : Complex.cos 1 ≠ 0 := by
  have h : (Real.cos 1 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt Real.cos_one_pos)
  simpa using h

theorem extremalConstant_exponential_identity :
    Complex.exp 1 + Complex.exp (-1) -
      extremalConstant * Complex.exp Complex.I -
      extremalConstant * Complex.exp (-Complex.I) = 0 := by
  have h := Complex.two_cos (1 : ℂ)
  simp only [one_mul, neg_mul, one_mul] at h
  have hc := Complex.two_cosh (1 : ℂ)
  have he : extremalConstant * Complex.cos 1 = Complex.cosh 1 := by
    exact div_mul_cancel₀ _ cos_one_ne_zero
  linear_combination -hc + extremalConstant * h - 2 * he

theorem extremalConstant_transcendental
    (lw : FourExponentialIndependence) : Transcendental ℚ extremalConstant := by
  intro halg
  have hc : ∀ j : Fin 4, IsAlgebraic ℚ
      (![1, 1, -extremalConstant, -extremalConstant] j) := by
    intro j
    fin_cases j
    · exact isAlgebraic_one
    · exact isAlgebraic_one
    · exact halg.neg
    · exact halg.neg
  have hs : (∑ j : Fin 4, (![1, 1, -extremalConstant, -extremalConstant] j) *
      Complex.exp (![1, -1, Complex.I, -Complex.I] j)) = 0 := by
    simpa [Fin.sum_univ_succ, sub_eq_add_neg, add_assoc] using
      extremalConstant_exponential_identity
  have hz := lw _ hc hs 0
  norm_num at hz

#print axioms extremalConstant_transcendental
end NonAlgebraicity
