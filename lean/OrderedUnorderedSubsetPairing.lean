import PairingRepresentativeBridge
import SubsetPairingScaling

noncomputable section
open scoped BigOperators
namespace OrderedUnorderedSubsetPairing

theorem weight_eq {L R S : Type*} [Fintype L] [Fintype R] [CommSemiring S]
    {a b : ℕ} (eL : L ≃ Fin a) (eR : R ≃ Fin b)
    (C : (L ⊕ R) → (L ⊕ R) → S) (hs : ∀ x y, C x y = C y x)
    (p : FinitePairingTransport.Pairing (L ⊕ R)) :
    FinitePairingTransport.weight eL eR C p = SymmetricPairingTransport.weight C hs p := by
  rw [PairingRepresentativeBridge.weight_eq_reps (FinitePairingTransport.key eL eR)
    (RectangularPairing.key_injective.comp (eL.sumCongr eR).injective)]
  rfl

theorem sum_eq {L R S : Type*} [Fintype L] [Fintype R] [CommSemiring S]
    {a b : ℕ} (eL : L ≃ Fin a) (eR : R ≃ Fin b)
    (C : (L ⊕ R) → (L ⊕ R) → S) (hs : ∀ x y, C x y = C y x) :
    (∑ p : FinitePairingTransport.Pairing (L ⊕ R), FinitePairingTransport.weight eL eR C p) =
      SymmetricPairingTransport.moment C hs := by
  apply Finset.sum_congr rfl
  intro p hp
  exact weight_eq eL eR C hs p

theorem covariance_symm {L R S : Type*} [CommSemiring S] (M : Matrix L R S) :
    ∀ x y, FinitePairingPermanent.covariance M x y = FinitePairingPermanent.covariance M y x := by
  intro x y
  cases x <;> cases y <;> rfl

theorem subsetWeight_eq {n : ℕ} {S : Type*} [CommSemiring S]
    (M : Matrix (Fin n) (Fin n) S) (I J : Finset (Fin n)) :
    SubsetPairingScaling.subsetWeight M I J =
      SymmetricPairingTransport.moment
        (FinitePairingPermanent.covariance (SubsetPairingPermanent.restriction M I J))
        (covariance_symm _) := by
  unfold SubsetPairingScaling.subsetWeight
  split
  · exact sum_eq _ _ _ _
  · exact sum_eq _ _ _ _

end OrderedUnorderedSubsetPairing
#print axioms OrderedUnorderedSubsetPairing.subsetWeight_eq
