import LinearSourceOccurrences
import Mathlib.Algebra.MvPolynomial.Basic

noncomputable section
open scoped BigOperators
namespace LinearSourceExpansion
open OccurrenceWickPolynomial LinearSourceOccurrences
variable {L S : Type*} [Fintype L] [DecidableEq L] [CommSemiring S]

def source (h : L → S) : MvPolynomial L S := ∑ i, h i • MvPolynomial.X i

theorem product_monomial {V : Type*} [Fintype V] (h : L → S) (a : V → L) :
    (∏ r, h (a r) • MvPolynomial.X (a r)) =
      MvPolynomial.monomial (exponent a) (∏ r, h (a r)) := by
  classical
  change (∏ r ∈ Finset.univ, _) = _
  have aux (t : Finset V) :
      (∏ r ∈ t, h (a r) • MvPolynomial.X (a r)) =
      MvPolynomial.monomial (∑ r ∈ t, Finsupp.single (a r) 1) (∏ r ∈ t, h (a r)) := by
    induction t using Finset.induction_on with
    | empty => simp
    | @insert r t hr ih =>
      simp only [Finset.prod_insert hr, Finset.sum_insert hr, ih]
      rw [MvPolynomial.X, MvPolynomial.smul_monomial]
      simp only [smul_eq_mul, mul_one, MvPolynomial.monomial_mul]
  exact aux _

theorem wick_source_power (C : L → L → S) (hs : ∀ i j, C i j = C j i)
    (h : L → S) (m : ℕ) :
    wick C hs ((source h)^m) =
      ∑ a : Fin m → L, (∏ r, h (a r)) *
        SymmetricPairingTransport.moment (fun r s : Fin m => C (a r) (a s))
          (fun r s => hs _ _) := by
  classical
  unfold source
  rw [Fintype.sum_pow, map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [product_monomial, wick_monomial, moment_assignment]

end LinearSourceExpansion
#print axioms LinearSourceExpansion.wick_source_power
