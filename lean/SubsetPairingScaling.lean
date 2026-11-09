import SubsetPairingPermanent

noncomputable section
open scoped BigOperators
namespace SubsetPairingScaling
open FinitePairingTransport SubsetPairingPermanent

/-- Both cases are genuine full pairing sums; equality of cardinalities
only selects aligned finite enumerations. -/
def subsetWeight {n : ℕ} {S : Type*} [CommSemiring S]
    (M : Matrix (Fin n) (Fin n) S) (I J : Finset (Fin n)) : S :=
  if h : I.card = J.card then
    ∑ p : Pairing (I ⊕ J), weight I.equivFin (J.equivFinOfCardEq h.symm)
      (FinitePairingPermanent.covariance (restriction M I J)) p
  else
    ∑ p : Pairing (I ⊕ J), weight I.equivFin J.equivFin
      (FinitePairingPermanent.covariance (restriction M I J)) p

def minor {n : ℕ} {S : Type*} (M : Matrix (Fin n) (Fin n) S)
    (I J : Finset (Fin n)) (h : I.card = J.card) : Matrix (Fin I.card) (Fin I.card) S :=
  FinitePairingPermanent.squareMatrix I.equivFin (J.equivFinOfCardEq h.symm)
    (restriction M I J)

theorem unequal {n : ℕ} {S : Type*} [CommSemiring S]
    (M : Matrix (Fin n) (Fin n) S) (I J : Finset (Fin n))
    (h : I.card ≠ J.card) : subsetWeight M I J = 0 := by
  rw [subsetWeight, dif_neg h]
  exact unequal_subsets_zero M I J h

theorem equal {n : ℕ} {S : Type*} [CommSemiring S]
    (M : Matrix (Fin n) (Fin n) S) (I J : Finset (Fin n))
    (h : I.card = J.card) : subsetWeight M I J = Matrix.permanent (minor M I J h) := by
  rw [subsetWeight, dif_pos h]
  exact FinitePairingPermanent.equal_sum_permanent _ _ _

theorem smul {n : ℕ} {S : Type*} [CommSemiring S]
    (M : Matrix (Fin n) (Fin n) S) (z : S) (I J : Finset (Fin n)) :
    subsetWeight (z • M) I J = z ^ I.card * subsetWeight M I J := by
  by_cases h : I.card = J.card
  · rw [equal _ _ _ h, equal _ _ _ h]
    have hm : minor (z • M) I J h = z • minor M I J h := rfl
    rw [hm, Matrix.permanent_smul]
    simp
  · rw [unequal _ _ _ h, unequal _ _ _ h, mul_zero]

end SubsetPairingScaling
#print axioms SubsetPairingScaling.smul
