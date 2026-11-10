import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.BigOperators
set_option autoImplicit false
/-! Minimal actual selected permanent and its unequal-cardinality boundary.
The two definitions/proofs are extracted verbatim from PermanentExpansion. -/
namespace TournamentHamiltonian
open scoped BigOperators
variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommSemiring R]
noncomputable def selectedPermanent (B : Matrix ι ι R) (s t : Finset ι) : R :=
  ∑ e : s ≃ t, ∏ i : s, B (e i) i


omit [Fintype ι] in
theorem selectedPermanent_eq_zero_of_card_ne (B : Matrix ι ι R) (s t : Finset ι)
    (h : s.card ≠ t.card) : selectedPermanent B s t = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro e _
  exact (h (by simpa using Fintype.card_congr e)).elim


end TournamentHamiltonian

set_option pp.fullNames true
#check TournamentHamiltonian.selectedPermanent
#print axioms TournamentHamiltonian.selectedPermanent
#check TournamentHamiltonian.selectedPermanent_eq_zero_of_card_ne
#print axioms TournamentHamiltonian.selectedPermanent_eq_zero_of_card_ne
