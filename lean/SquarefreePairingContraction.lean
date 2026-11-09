import FrozenPartialPairingPolynomial
import ShiftedProductSubsetExpansion

noncomputable section
open scoped BigOperators
namespace SquarefreePairingContraction
open SubsetPairingScaling FrozenPartialPairingPolynomial

def exponent {n : ℕ} (I J : Finset (Fin n)) : (Fin n ⊕ Fin n) →₀ ℕ :=
  (∑ i ∈ I, Finsupp.single (Sum.inl i) 1) + ∑ j ∈ J, Finsupp.single (Sum.inr j) 1

theorem exponent_left {n : ℕ} (I J : Finset (Fin n)) (i : Fin n) :
    exponent I J (Sum.inl i) = if i ∈ I then 1 else 0 := by
  simp [exponent, Finsupp.single_apply]

theorem exponent_right {n : ℕ} (I J : Finset (Fin n)) (j : Fin n) :
    exponent I J (Sum.inr j) = if j ∈ J then 1 else 0 := by
  simp [exponent, Finsupp.single_apply]

theorem exponent_eq_iff {n : ℕ} (I J I' J' : Finset (Fin n)) :
    exponent I J = exponent I' J' ↔ I = I' ∧ J = J' := by
  constructor
  · intro h
    constructor
    · ext i
      have hi := congrArg (fun f => f (Sum.inl i)) h
      rw [exponent_left,exponent_left] at hi
      by_cases h1 : i ∈ I <;> by_cases h2 : i ∈ I' <;> simp_all
    · ext j
      have hj := congrArg (fun f => f (Sum.inr j)) h
      rw [exponent_right,exponent_right] at hj
      by_cases h1 : j ∈ J <;> by_cases h2 : j ∈ J' <;> simp_all
  · rintro ⟨rfl,rfl⟩; rfl

/-- Finite squarefree coefficient contraction; not a probability expectation.
Nonsquarefree monomials are ignored by this explicitly defined linear map. -/
def contraction {n : ℕ} {S : Type*} [CommSemiring S]
    (M : Matrix (Fin n) (Fin n) S) : MvPolynomial (Fin n ⊕ Fin n) S →ₗ[S] S :=
  ∑ I ∈ Finset.univ.powerset, ∑ J ∈ Finset.univ.powerset,
    subsetWeight M I J • MvPolynomial.lcoeff S (exponent I J)

theorem contraction_monomial {n : ℕ} {S : Type*} [CommSemiring S]
    (M : Matrix (Fin n) (Fin n) S) (I J : Finset (Fin n)) :
    contraction M (MvPolynomial.monomial (exponent I J) 1) = subsetWeight M I J := by
  classical
  simp [contraction, MvPolynomial.lcoeff, MvPolynomial.coeff_monomial,
    exponent_eq_iff, ite_and]

theorem product_monomial {n : ℕ} {S : Type*} [CommSemiring S]
    (I J : Finset (Fin n)) :
    (∏ i ∈ I, MvPolynomial.X (Sum.inl i) : MvPolynomial (Fin n ⊕ Fin n) S) *
      (∏ j ∈ J, MvPolynomial.X (Sum.inr j)) =
        MvPolynomial.monomial (exponent I J) 1 := by
  classical
  have hp (f : Fin n → Fin n ⊕ Fin n) (s : Finset (Fin n)) :
      (∏ i ∈ s, MvPolynomial.X (f i) : MvPolynomial (Fin n ⊕ Fin n) S) =
        MvPolynomial.monomial (∑ i ∈ s, Finsupp.single (f i) 1) 1 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih]
      simp [MvPolynomial.X, MvPolynomial.monomial_mul_monomial]
  rw [hp, hp, MvPolynomial.monomial_mul_monomial]
  simp [exponent]

theorem contraction_shifted_product {n : ℕ} {S : Type*} [CommSemiring S]
    (M : Matrix (Fin n) (Fin n) S) :
    contraction M (∏ x : Fin n ⊕ Fin n, (1 + MvPolynomial.X x)) = globalWeight M := by
  rw [ShiftedProductSubsetExpansion.polynomial_expansion]
  simp_rw [map_sum, product_monomial, contraction_monomial]
  rfl

theorem contraction_scaled_product {n : ℕ} {S : Type*} [CommSemiring S]
    (M : Matrix (Fin n) (Fin n) S) (z : S) :
    contraction (z • M) (∏ x : Fin n ⊕ Fin n, (1 + MvPolynomial.X x)) =
      (frozenPolynomial M).eval z := by
  rw [contraction_shifted_product, eval_frozenPolynomial]

end SquarefreePairingContraction
#print axioms SquarefreePairingContraction.contraction_shifted_product
#print axioms SquarefreePairingContraction.contraction_scaled_product
