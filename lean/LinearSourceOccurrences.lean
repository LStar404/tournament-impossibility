import OccurrenceWickPolynomial
import Mathlib.Algebra.BigOperators.Ring.Finset

noncomputable section
open scoped BigOperators
namespace LinearSourceOccurrences
open OccurrenceWickPolynomial
variable {L V S : Type*} [Fintype L] [Fintype V] [DecidableEq L]

/-- Multiplicity of each label in an actual assignment of positions. -/
def exponent (a : V → L) : L →₀ ℕ := ∑ r : V, Finsupp.single (a r) 1

theorem exponent_eq_card (a : V → L) (i : L) :
    exponent a i = Fintype.card {r : V // a r = i} := by
  classical
  simp [exponent, Finsupp.sum_apply, Finsupp.single_apply, Fintype.card_subtype,
    eq_comm]

/-- Occurrences are enumerated by the actual assignment fibres. -/
def fibreEquiv (a : V → L) (i : L) :
    Fin (exponent a i) ≃ {r : V // a r = i} :=
  (finCongr (exponent_eq_card a i)).trans (Fintype.equivFin _).symm

def occurrenceEquiv (a : V → L) : Occ (exponent a) ≃ V where
  toFun x := (fibreEquiv a x.1 x.2).val
  invFun r := ⟨a r, (fibreEquiv a (a r)).symm ⟨r, rfl⟩⟩
  left_inv := by
    rintro ⟨i,k⟩
    dsimp
    generalize h : fibreEquiv a i k = r
    rcases r with ⟨r,hr⟩
    dsimp at *
    subst i
    congr 1
    exact (Equiv.symm_apply_eq (fibreEquiv a (a r))).mpr h.symm
  right_inv r := by simp

theorem occurrenceEquiv_label (a : V → L) (r : V) :
    ((occurrenceEquiv a).symm r).1 = a r := rfl

theorem moment_assignment [CommSemiring S] (C : L → L → S)
    (hs : ∀ i j, C i j = C j i) (a : V → L) :
    monomialMoment C hs (exponent a) =
      SymmetricPairingTransport.moment (fun r s : V => C (a r) (a s))
        (fun r s => hs _ _) := by
  exact monomialMoment_enumeration C hs (exponent a) (occurrenceEquiv a)

end LinearSourceOccurrences
#print axioms LinearSourceOccurrences.moment_assignment
