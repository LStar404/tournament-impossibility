import OptionPairingDeletion

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.typeDecidableEq
namespace FullWickMonomialRecurrence
open OccurrenceWickPolynomial LinearSourceOccurrences AssignmentDeletionExponent
variable {L V S : Type*} [Fintype L] [Fintype V] [CommSemiring S]

theorem assignment_recurrence (C : L → L → S) (hs : ∀ i j, C i j = C j i)
    (i : L) (a : V → L) :
    monomialMoment C hs (Finsupp.single i 1 + exponent a) =
      ∑ x : V, C i (a x) * monomialMoment C hs (exponent a - Finsupp.single (a x) 1) := by
  rw [← option_exponent i a, moment_assignment, OptionPairingDeletion.option_moment]
  apply Finset.sum_congr rfl
  intro x _
  rw [← delete_sub a x, moment_assignment]

theorem monomial_recurrence (C : L → L → S) (hs : ∀ i j, C i j = C j i)
    (i : L) (d : L →₀ ℕ) :
    monomialMoment C hs (Finsupp.single i 1 + d) =
      ∑ j : L, (d j : S) * C i j * monomialMoment C hs (d - Finsupp.single j 1) := by
  have hh := assignment_recurrence C hs i (fun x : Occ d => x.1)
  rw [occurrence_exponent] at hh
  rw [hh, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  simp [nsmul_eq_mul, mul_assoc]

end FullWickMonomialRecurrence
#print axioms FullWickMonomialRecurrence.monomial_recurrence
