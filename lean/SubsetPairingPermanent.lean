import FinitePairingPermanent

noncomputable section
open scoped BigOperators
namespace SubsetPairingPermanent
open FinitePairingTransport

/-- The selected covariance is restricted before the pairing sum is taken. -/
def restriction {n : ℕ} {S : Type*} (A : Matrix (Fin n) (Fin n) S)
    (I J : Finset (Fin n)) : Matrix I J S := fun i j => A i.val j.val

theorem unequal_subsets_zero {n : ℕ} {S : Type*} [CommSemiring S]
    (A : Matrix (Fin n) (Fin n) S) (I J : Finset (Fin n)) (h : I.card ≠ J.card) :
    ∑ p : Pairing (I ⊕ J), weight I.equivFin J.equivFin
      (FinitePairingPermanent.covariance (restriction A I J)) p = 0 :=
  FinitePairingPermanent.unequal_sum_zero I.equivFin J.equivFin (restriction A I J) h

theorem equal_subsets_permanent {n k : ℕ} {S : Type*} [CommSemiring S]
    (A : Matrix (Fin n) (Fin n) S) (I J : Finset (Fin n))
    (hI : I.card = k) (hJ : J.card = k) :
    ∑ p : Pairing (I ⊕ J), weight (I.equivFinOfCardEq hI) (J.equivFinOfCardEq hJ)
      (FinitePairingPermanent.covariance (restriction A I J)) p =
    Matrix.permanent (FinitePairingPermanent.squareMatrix
      (I.equivFinOfCardEq hI) (J.equivFinOfCardEq hJ) (restriction A I J)) :=
  FinitePairingPermanent.equal_sum_permanent
    (I.equivFinOfCardEq hI) (J.equivFinOfCardEq hJ) (restriction A I J)

end SubsetPairingPermanent
#print axioms SubsetPairingPermanent.unequal_subsets_zero
#print axioms SubsetPairingPermanent.equal_subsets_permanent
