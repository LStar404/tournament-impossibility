import FinitePairingTransport
import Mathlib.Data.Sym.Sym2

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.typeDecidableEq
namespace SymmetricPairingTransport
open FinitePairingTransport

/-- The finite set of unordered edges of a genuine partner involution. -/
def edges {V : Type*} [Fintype V] (p : Pairing V) : Finset (Sym2 V) := by
  classical
  exact Finset.univ.image (fun x => Sym2.mk x (p.val x))

def weight {V S : Type*} [Fintype V] [CommSemiring S]
    (C : V → V → S) (hs : ∀ x y, C x y = C y x) (p : Pairing V) : S :=
  ∏ b ∈ edges p, Sym2.lift ⟨C,hs⟩ b

def moment {V S : Type*} [Fintype V] [CommSemiring S]
    (C : V → V → S) (hs : ∀ x y, C x y = C y x) : S :=
  ∑ p : Pairing V, weight C hs p

theorem edge_transport {V W : Type*} [Fintype V] [Fintype W]
    (e : V ≃ W) (p : Pairing V) :
    edges (transport e p) = (edges p).image (Sym2.map e) := by
  classical
  ext b
  simp only [edges, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨w,rfl⟩
    refine ⟨Sym2.mk (e.symm w) (p.val (e.symm w)),⟨e.symm w,rfl⟩,?_⟩
    simp [transport, Equiv.permCongr_def]
  · rintro ⟨b,⟨v,rfl⟩,rfl⟩
    refine ⟨e v,?_⟩
    simp [transport, Equiv.permCongr_def]

theorem weight_transport {V W S : Type*} [Fintype V] [Fintype W] [CommSemiring S]
    (e : V ≃ W) (C : V → V → S) (hs : ∀ x y, C x y = C y x) (p : Pairing V) :
    weight C hs p = weight (fun x y => C (e.symm x) (e.symm y))
      (fun x y => hs _ _) (transport e p) := by
  classical
  unfold weight
  rw [edge_transport, Finset.prod_image]
  · apply Finset.prod_congr rfl
    intro b hb
    induction b using Sym2.ind with
    | _ x y => simp
  · intro a ha b hb h
    exact Sym2.map.injective e.injective h

/-- Arbitrary occurrence reindexing; there is no colour restriction. -/
theorem moment_transport {V W S : Type*} [Fintype V] [Fintype W] [CommSemiring S]
    (e : V ≃ W) (C : V → V → S) (hs : ∀ x y, C x y = C y x) :
    moment C hs = moment (fun x y => C (e.symm x) (e.symm y)) (fun x y => hs _ _) := by
  classical
  exact Fintype.sum_equiv (transportEquiv e) _ _ (fun p => weight_transport e C hs p)

end SymmetricPairingTransport
#print axioms SymmetricPairingTransport.moment_transport
