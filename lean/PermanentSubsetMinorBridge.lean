import FrozenPartialPairingPolynomial
import Mathlib.Logic.Equiv.Fintype

/-!
Exact finite comparison of actual selected-minor and pairing definitions.
The normalization of the actual permanent is a separate subsequent theorem.

The selected index order is COLUMN set, then ROW set. The existing
SubsetPairingScaling.subsetWeight uses ROW set, then COLUMN set.
Consequently the sets must be swapped in the connecting theorem.
-/
noncomputable section
open scoped BigOperators

namespace PermanentSubsetMinorBridge

variable {n : ℕ} {S : Type*} [CommSemiring S]

/-- Same finite definition as the upstream `selectedPermanent`. -/
def selectedPermanent (M : Matrix (Fin n) (Fin n) S)
    (I J : Finset (Fin n)) : S :=
  ∑ p : I ≃ J, ∏ i : I, M (p i) i

/-- The orientation bridge; there is no extra factorial or pairing factor. -/
theorem selected_eq_subsetWeight (M : Matrix (Fin n) (Fin n) S)
    (I J : Finset (Fin n)) :
    selectedPermanent M I J = SubsetPairingScaling.subsetWeight M J I := by
  classical
  by_cases h : I.card = J.card
  · rw [SubsetPairingScaling.equal M J I h.symm]
    unfold selectedPermanent Matrix.permanent
    apply Fintype.sum_equiv
      (Equiv.equivCongr (I.equivFinOfCardEq h) J.equivFin)
    intro p
    apply Fintype.prod_equiv (I.equivFinOfCardEq h)
    intro i
    simp [SubsetPairingScaling.minor, FinitePairingPermanent.squareMatrix,
      SubsetPairingPermanent.restriction, Equiv.equivCongr_apply_apply]
  · rw [SubsetPairingScaling.unequal M J I (Ne.symm h)]
    unfold selectedPermanent
    apply Finset.sum_eq_zero
    intro p hp
    exact False.elim (h (by simpa using Fintype.card_congr p))

/-- A minor sum using exactly the existing powerset-card indexing. -/
def minorSum (M : Matrix (Fin n) (Fin n) S) (k : ℕ) : S :=
  ∑ I ∈ Finset.univ.powersetCard k,
    ∑ J ∈ Finset.univ.powersetCard k, selectedPermanent M I J

theorem Fk_eq_minorSum (M : Matrix (Fin n) (Fin n) S) (k : ℕ) :
    FrozenPartialPairingPolynomial.Fk M k = minorSum M k := by
  classical
  unfold FrozenPartialPairingPolynomial.Fk minorSum
  simp_rw [selected_eq_subsetWeight]
  exact Finset.sum_comm

/-- Needed before extending a coefficient identity beyond k <= n. -/
theorem Fk_zero_above_dimension (M : Matrix (Fin n) (Fin n) S)
    (k : ℕ) (hk : n < k) : FrozenPartialPairingPolynomial.Fk M k = 0 := by
  classical
  have he : (Finset.univ : Finset (Fin n)).powersetCard k = ∅ :=
    Finset.powersetCard_eq_empty.mpr (by simpa using hk)
  simp [FrozenPartialPairingPolynomial.Fk, he]

end PermanentSubsetMinorBridge

#print axioms PermanentSubsetMinorBridge.selected_eq_subsetWeight
#print axioms PermanentSubsetMinorBridge.Fk_eq_minorSum
