import PairingMomentRecurrence
import Mathlib.Combinatorics.SimpleGraph.Matching

noncomputable section
namespace PairingMomentParity
open FinitePairingTransport SymmetricPairingTransport

def graph {V : Type*} (p : Pairing V) : SimpleGraph V where
  Adj x y := p.val x = y
  symm := ⟨by
    intro x y h
    rw [← h,p.property.1]⟩
  loopless := ⟨fun x => p.property.2 x⟩

theorem pairing_even {V : Type*} [Fintype V] (p : Pairing V) : Even (Fintype.card V) := by
  have h : (⊤ : (graph p).Subgraph).IsPerfectMatching := by
    rw [SimpleGraph.Subgraph.isPerfectMatching_iff]
    intro x
    refine ⟨p.val x,?_,?_⟩
    · exact rfl
    · intro y hy
      change p.val x = y at hy
      exact hy.symm
  exact h.even_card

theorem odd_moment_zero {V S : Type*} [Fintype V] [CommSemiring S]
    (C : V → V → S) (hc : ∀ x y, C x y = C y x) (hodd : Odd (Fintype.card V)) :
    moment C hc = 0 := by
  classical
  letI : IsEmpty (Pairing V) := ⟨fun p => (Nat.not_even_iff_odd.mpr hodd) (pairing_even p)⟩
  simp [moment]

theorem empty_moment_one {V S : Type*} [Fintype V] [IsEmpty V] [CommSemiring S]
    (C : V → V → S) (hc : ∀ x y, C x y = C y x) : moment C hc = 1 := by
  classical
  let p0 : Pairing V := ⟨Equiv.refl V,by constructor <;> intro x <;> exact isEmptyElim x⟩
  letI : Unique (Pairing V) := ⟨⟨p0⟩,fun p => Subsingleton.elim _ _⟩
  simp [moment,SymmetricPairingTransport.weight,edges]

end PairingMomentParity
#print axioms PairingMomentParity.pairing_even
#print axioms PairingMomentParity.odd_moment_zero
#print axioms PairingMomentParity.empty_moment_one
