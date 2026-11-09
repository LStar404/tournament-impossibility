import SymmetricPairingTransport
import RepeatedLabelPairing

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.typeDecidableEq
namespace PairingRepresentativeBridge
open FinitePairingTransport

def reps {V : Type*} [Fintype V] (rank : V → ℕ) (p : Pairing V) : Finset V :=
  Finset.univ.filter (fun x => rank x < rank (p.val x))

theorem edges_eq_image {V : Type*} [Fintype V] (rank : V → ℕ)
    (hi : Function.Injective rank) (p : Pairing V) :
    SymmetricPairingTransport.edges p = (reps rank p).image (fun x => Sym2.mk x (p.val x)) := by
  ext b
  simp only [SymmetricPairingTransport.edges, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x,rfl⟩
    have hn : rank x ≠ rank (p.val x) := fun h => p.property.2 x (hi h).symm
    rcases lt_or_gt_of_ne hn with h | h
    · exact ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩,rfl⟩
    · refine ⟨p.val x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩
      · simpa only [p.property.1 x] using h
      · rw [p.property.1 x]; exact Sym2.eq_swap
  · rintro ⟨x,hx,rfl⟩
    exact ⟨x,rfl⟩

theorem edge_injective_on_reps {V : Type*} [Fintype V] (rank : V → ℕ)
    (p : Pairing V) : Set.InjOn (fun x => Sym2.mk x (p.val x)) (reps rank p) := by
  intro x hx y hy h
  have hxl := (Finset.mem_filter.mp hx).2
  have hyl := (Finset.mem_filter.mp hy).2
  rcases Sym2.eq_iff.mp h with h | h
  · exact h.1
  · have h1 := congrArg rank h.1
    have h2 := congrArg rank h.2
    omega

theorem weight_eq_reps {V S : Type*} [Fintype V] [CommSemiring S]
    (rank : V → ℕ) (hi : Function.Injective rank)
    (C : V → V → S) (hs : ∀ x y, C x y = C y x) (p : Pairing V) :
    SymmetricPairingTransport.weight C hs p = ∏ x ∈ reps rank p, C x (p.val x) := by
  unfold SymmetricPairingTransport.weight
  rw [edges_eq_image rank hi, Finset.prod_image (edge_injective_on_reps rank p)]
  apply Finset.prod_congr rfl
  intro x hx
  exact Sym2.lift_mk _ _ _

/-- Equality with the earlier ordered-position definition, for every
symmetric covariance, without any zero same-colour hypothesis. -/
theorem occurrence_moment_eq {n : ℕ} {L S : Type*} [CommSemiring S]
    (C : L → L → S) (hs : ∀ x y, C x y = C y x)
    (a : Fin n ⊕ Fin n → L) :
    RepeatedLabelPairing.moment C a =
      SymmetricPairingTransport.moment (fun i j => C (a i) (a j)) (fun i j => hs _ _) := by
  unfold RepeatedLabelPairing.moment SymmetricPairingTransport.moment
  have hw (p : Pairing (Fin n ⊕ Fin n)) :
      WickPairingZero.weight (fun i j => C (a i) (a j)) p =
        SymmetricPairingTransport.weight (fun i j => C (a i) (a j)) (fun i j => hs _ _) p := by
    rw [weight_eq_reps WickPairingZero.key WickPairingZero.key_injective]
    rfl
  convert (Finset.sum_congr rfl (fun p _ => hw p)) using 1
  congr 1
  ext p
  simp

/-- Arbitrary mixed-colour permutations are permitted; symmetry handles
reversal of the former minimum-endpoint representatives. -/
theorem arbitrary_reordering {n : ℕ} {L S : Type*} [CommSemiring S]
    (C : L → L → S) (hs : ∀ x y, C x y = C y x)
    (a : Fin n ⊕ Fin n → L) (e : Equiv.Perm (Fin n ⊕ Fin n)) :
    RepeatedLabelPairing.moment C (a ∘ e) = RepeatedLabelPairing.moment C a := by
  rw [occurrence_moment_eq C hs, occurrence_moment_eq C hs]
  simpa [Function.comp_def] using
    (SymmetricPairingTransport.moment_transport e.symm
      (fun i j => C (a i) (a j)) (fun i j => hs _ _)).symm

end PairingRepresentativeBridge
#print axioms PairingRepresentativeBridge.occurrence_moment_eq

#print axioms PairingRepresentativeBridge.arbitrary_reordering
