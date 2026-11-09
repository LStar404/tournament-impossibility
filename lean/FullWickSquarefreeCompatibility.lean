import OccurrenceSquarefreeEquiv
import OrderedUnorderedSubsetPairing

noncomputable section
open scoped BigOperators
namespace FullWickSquarefreeCompatibility
open SquarefreePairingContraction OccurrenceWickPolynomial
open SubsetPairingScaling FrozenPartialPairingPolynomial

def block {n : ℕ} {S : Type*} [CommSemiring S] (M : Matrix (Fin n) (Fin n) S) :
    (Fin n ⊕ Fin n) → (Fin n ⊕ Fin n) → S :=
  fun x y => FinitePairingPermanent.covariance M x y

theorem block_symm {n : ℕ} {S : Type*} [CommSemiring S] (M : Matrix (Fin n) (Fin n) S) :
    ∀ x y, block M x y = block M y x := OrderedUnorderedSubsetPairing.covariance_symm M

theorem monomialMoment_eq {n : ℕ} {S : Type*} [CommSemiring S]
    (M : Matrix (Fin n) (Fin n) S) (I J : Finset (Fin n)) :
    monomialMoment (block M) (block_symm M) (exponent I J) = subsetWeight M I J := by
  have h := monomialMoment_enumeration (block M) (block_symm M) (exponent I J)
    (OccurrenceSquarefreeEquiv.equivalence I J)
  have hc : (fun x y : I ⊕ J => block M
      ((OccurrenceSquarefreeEquiv.equivalence I J).symm x).1
      ((OccurrenceSquarefreeEquiv.equivalence I J).symm y).1) =
      FinitePairingPermanent.covariance (SubsetPairingPermanent.restriction M I J) := by
    funext x y
    rw [OccurrenceSquarefreeEquiv.inverse_label,OccurrenceSquarefreeEquiv.inverse_label]
    cases x <;> cases y <;> rfl
  apply h.trans
  rw [OrderedUnorderedSubsetPairing.subsetWeight_eq]
  congr 1

theorem wick_squarefree_monomial {n : ℕ} {S : Type*} [CommSemiring S]
    (M : Matrix (Fin n) (Fin n) S) (I J : Finset (Fin n)) :
    wick (block M) (block_symm M) (MvPolynomial.monomial (exponent I J) 1) =
      contraction M (MvPolynomial.monomial (exponent I J) 1) := by
  rw [wick_monomial,monomialMoment_eq,one_mul,contraction_monomial]

theorem wick_shifted_product {n : ℕ} {S : Type*} [CommSemiring S]
    (M : Matrix (Fin n) (Fin n) S) :
    wick (block M) (block_symm M) (∏ x : Fin n ⊕ Fin n, (1 + MvPolynomial.X x)) =
      globalWeight M := by
  rw [ShiftedProductSubsetExpansion.polynomial_expansion]
  simp_rw [map_sum, product_monomial, wick_squarefree_monomial, contraction_monomial]
  rfl

theorem wick_scaled_product {n : ℕ} {S : Type*} [CommSemiring S]
    (M : Matrix (Fin n) (Fin n) S) (z : S) :
    wick (block (z • M)) (block_symm (z • M))
      (∏ x : Fin n ⊕ Fin n, (1 + MvPolynomial.X x)) = (frozenPolynomial M).eval z := by
  rw [wick_shifted_product,eval_frozenPolynomial]

end FullWickSquarefreeCompatibility
#print axioms FullWickSquarefreeCompatibility.wick_squarefree_monomial
#print axioms FullWickSquarefreeCompatibility.wick_scaled_product
