import Mathlib

noncomputable section
open scoped BigOperators
namespace ShiftedProductSubsetExpansion

/-- Universal finite algebra, not a moment identification. -/
theorem split_product {n : ℕ} {S : Type*} [CommSemiring S]
    (X : Fin n ⊕ Fin n → S) :
    (∏ x, (1 + X x)) =
      ∑ I ∈ (Finset.univ : Finset (Fin n)).powerset,
        ∑ J ∈ (Finset.univ : Finset (Fin n)).powerset,
          (∏ i ∈ I, X (Sum.inl i)) * (∏ j ∈ J, X (Sum.inr j)) := by
  rw [Fintype.prod_sum_type]
  rw [Finset.prod_one_add, Finset.prod_one_add]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro I hI
  rw [Finset.mul_sum]

/-- In particular the expansion holds as a multivariate polynomial identity. -/
theorem polynomial_expansion (n : ℕ) (S : Type*) [CommSemiring S] :
    (∏ x : Fin n ⊕ Fin n, (1 + MvPolynomial.X x : MvPolynomial (Fin n ⊕ Fin n) S)) =
      ∑ I ∈ (Finset.univ : Finset (Fin n)).powerset,
        ∑ J ∈ (Finset.univ : Finset (Fin n)).powerset,
          (∏ i ∈ I, MvPolynomial.X (Sum.inl i)) *
            (∏ j ∈ J, MvPolynomial.X (Sum.inr j)) :=
  split_product MvPolynomial.X

end ShiftedProductSubsetExpansion
#print axioms ShiftedProductSubsetExpansion.polynomial_expansion
