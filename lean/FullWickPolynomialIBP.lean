import FullWickMonomialRecurrence
import Mathlib.Algebra.MvPolynomial.PDeriv

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.typeDecidableEq
namespace FullWickPolynomialIBP
open OccurrenceWickPolynomial FullWickMonomialRecurrence
variable {L S : Type*} [Fintype L] [CommSemiring S]

/-- Formal Gaussian integration by parts for the actual full pairing
functional. This is an algebraic polynomial identity, not a measure claim. -/
theorem wick_X_mul (C : L → L → S) (hs : ∀ i j, C i j = C j i)
    (i : L) (P : MvPolynomial L S) :
    wick C hs (MvPolynomial.X i * P) =
      ∑ j : L, C i j * wick C hs (MvPolynomial.pderiv j P) := by
  induction P using MvPolynomial.induction_on' with
  | monomial d a =>
    rw [MvPolynomial.X, MvPolynomial.monomial_mul_monomial, wick_monomial,
      one_mul, monomial_recurrence, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [MvPolynomial.pderiv_monomial, wick_monomial]
    ring
  | add P Q hP hQ =>
    simp only [mul_add, map_add, hP, hQ, Finset.sum_add_distrib]

end FullWickPolynomialIBP
#print axioms FullWickPolynomialIBP.wick_X_mul
