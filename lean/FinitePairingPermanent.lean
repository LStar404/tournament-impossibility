import FinitePairingTransport

noncomputable section
open scoped BigOperators
namespace FinitePairingPermanent
open FinitePairingTransport

def covariance {L R S : Type*} [CommSemiring S]
    (A : Matrix L R S) : Matrix (L ⊕ R) (L ⊕ R) S :=
  Matrix.fromBlocks 0 A A.transpose 0

def squareMatrix {L R S : Type*} {k : ℕ} (eL : L ≃ Fin k) (eR : R ≃ Fin k)
    (A : Matrix L R S) : Matrix (Fin k) (Fin k) S :=
  fun i j => A (eL.symm i) (eR.symm j)

theorem unequal_sum_zero {L R S : Type*} [Fintype L] [Fintype R] [CommSemiring S]
    {a b : ℕ} (eL : L ≃ Fin a) (eR : R ≃ Fin b)
    (A : Matrix L R S) (hab : a ≠ b) :
    ∑ p : Pairing (L ⊕ R), weight eL eR (covariance A) p = 0 := by
  classical
  rw [sum_transport]
  have hz : ∀ x y, RectangularPairing.color x = RectangularPairing.color y →
      transportedMatrix eL eR (covariance A) x y = 0 := by
    intro x y h
    cases x <;> cases y <;>
      simp_all [RectangularPairing.color, transportedMatrix, covariance]
  have h := RectangularPairing.unequal_sum_zero _ hz hab
  convert h using 1
  congr 1
  ext p
  simp

theorem equal_sum_permanent {L R S : Type*} [Fintype L] [Fintype R] [CommSemiring S]
    {k : ℕ} (eL : L ≃ Fin k) (eR : R ≃ Fin k) (A : Matrix L R S) :
    ∑ p : Pairing (L ⊕ R), weight eL eR (covariance A) p =
      Matrix.permanent (squareMatrix eL eR A) := by
  classical
  rw [sum_transport]
  have hC : transportedMatrix eL eR (covariance A) =
      WickPairingPermanent.covariance (squareMatrix eL eR A) := by
    ext x y
    cases x <;> cases y <;> rfl
  rw [hC]
  convert WickPairingPermanent.all_pairings_eq_permanent (squareMatrix eL eR A) using 1
  congr 1
  · ext p; simp
  · funext p
    unfold RectangularPairing.weight WickPairingZero.weight
    congr 1
    ext x
    simp only [RectangularPairing.representatives, WickPairingZero.representatives,
      Finset.mem_filter, Finset.mem_univ, true_and]
    cases x <;> cases p.val _ <;> rfl

end FinitePairingPermanent
#print axioms FinitePairingPermanent.unequal_sum_zero
#print axioms FinitePairingPermanent.equal_sum_permanent
