import PairingRepresentativeBridge
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

noncomputable section
open scoped BigOperators
namespace OccurrenceWickPolynomial

/-- Each coordinate has d(i) separate occurrences, not one support element. -/
abbrev Occ {L : Type*} (d : L →₀ ℕ) := Σ i : L, Fin (d i)

def monomialMoment {L S : Type*} [Fintype L] [CommSemiring S]
    (C : L → L → S) (hs : ∀ x y, C x y = C y x) (d : L →₀ ℕ) : S :=
  SymmetricPairingTransport.moment (fun x y : Occ d => C x.1 y.1)
    (fun x y => hs _ _)

/-- Full formal polynomial pairing functional. This is not a probability
expectation; unlike the squarefree projection it retains repeated indices. -/
def wick {L S : Type*} [Fintype L] [CommSemiring S]
    (C : L → L → S) (hs : ∀ x y, C x y = C y x) : MvPolynomial L S →ₗ[S] S :=
  (Finsupp.linearCombination S (monomialMoment C hs)).comp
    (AddMonoidAlgebra.coeffLinearEquiv S).toLinearMap

theorem wick_monomial {L S : Type*} [Fintype L] [CommSemiring S]
    (C : L → L → S) (hs : ∀ x y, C x y = C y x) (d : L →₀ ℕ) (c : S) :
    wick C hs (MvPolynomial.monomial d c) = c * monomialMoment C hs d := by
  simp [wick, MvPolynomial.monomial, Finsupp.linearCombination_apply]

/-- Any actual enumeration of occurrence positions computes the same
monomial moment, with no rank-preservation or colour hypothesis. -/
theorem monomialMoment_enumeration {L S V : Type*} [Fintype L] [Fintype V]
    [CommSemiring S] (C : L → L → S) (hs : ∀ x y, C x y = C y x)
    (d : L →₀ ℕ) (e : Occ d ≃ V) :
    monomialMoment C hs d =
      SymmetricPairingTransport.moment (fun x y : V => C (e.symm x).1 (e.symm y).1)
        (fun x y => hs _ _) :=
  SymmetricPairingTransport.moment_transport e _ _

end OccurrenceWickPolynomial
#print axioms OccurrenceWickPolynomial.wick_monomial
#print axioms OccurrenceWickPolynomial.monomialMoment_enumeration
