import FrozenPartialPairingPolynomial
import Mathlib.Algebra.Polynomial.BigOperators

noncomputable section
open scoped BigOperators
namespace FrozenPairingEndpoints
open FrozenPartialPairingPolynomial SubsetPairingScaling

theorem F0 {n : ℕ} {S : Type*} [CommSemiring S]
    (M : Matrix (Fin n) (Fin n) S) : Fk M 0 = 1 := by
  simp only [Fk, Finset.powersetCard_zero, Finset.sum_singleton]
  rw [equal M ∅ ∅ rfl]
  apply Matrix.permanent_eq_one_of_card_eq_zero
  simp only [Finset.card_empty]
  exact Fintype.card_eq_zero

theorem natDegree_le {n : ℕ} {S : Type*} [CommSemiring S]
    (M : Matrix (Fin n) (Fin n) S) : (frozenPolynomial M).natDegree ≤ n := by
  unfold frozenPolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  exact (Polynomial.natDegree_monomial_le _).trans (Nat.le_of_lt_succ (Finset.mem_range.mp hk))

theorem degree_le {n : ℕ} {S : Type*} [CommSemiring S]
    (M : Matrix (Fin n) (Fin n) S) : (frozenPolynomial M).degree ≤ n :=
  Polynomial.degree_le_of_natDegree_le (natDegree_le M)

end FrozenPairingEndpoints
#print axioms FrozenPairingEndpoints.F0
#print axioms FrozenPairingEndpoints.degree_le
