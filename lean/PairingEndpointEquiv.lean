import PairingRepresentativeBridge

noncomputable section
namespace PairingEndpointEquiv
open FinitePairingTransport PairingRepresentativeBridge
variable {V : Type*} [Fintype V]

def endpoint (rank : V → ℕ) (p : Pairing V) : (reps rank p) × Bool → V
  | (x,false) => x.val
  | (x,true) => p.val x.val

theorem endpoint_injective (rank : V → ℕ) (p : Pairing V) :
    Function.Injective (endpoint rank p) := by
  rintro ⟨⟨x,hx⟩,b⟩ ⟨⟨y,hy⟩,c⟩ h
  have hx' := (Finset.mem_filter.mp hx).2
  have hy' := (Finset.mem_filter.mp hy).2
  cases b <;> cases c <;> simp only [endpoint] at h
  · subst y; rfl
  · have hh := congrArg p.val h
    rw [p.property.1] at hh
    have h1 := congrArg rank h
    have h2 := congrArg rank hh
    omega
  · have hh := congrArg p.val h
    rw [p.property.1] at hh
    have h1 := congrArg rank h
    have h2 := congrArg rank hh
    omega
  · have hh := p.val.injective h
    subst y; rfl

theorem endpoint_surjective (rank : V → ℕ) (hi : Function.Injective rank)
    (p : Pairing V) : Function.Surjective (endpoint rank p) := by
  intro x
  have hn : rank x ≠ rank (p.val x) := fun h => p.property.2 x (hi h).symm
  rcases lt_or_gt_of_ne hn with h | h
  · exact ⟨(⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩⟩,false),rfl⟩
  · refine ⟨(⟨p.val x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩,true),?_⟩
    · simpa only [p.property.1] using h
    · exact p.property.1 x

def equivalence (rank : V → ℕ) (hi : Function.Injective rank) (p : Pairing V) :
    (reps rank p) × Bool ≃ V :=
  Equiv.ofBijective (endpoint rank p) ⟨endpoint_injective rank p,endpoint_surjective rank hi p⟩

theorem card_eq (rank : V → ℕ) (hi : Function.Injective rank) (p : Pairing V) :
    Fintype.card V = (reps rank p).card * 2 := by
  rw [← Fintype.card_congr (equivalence rank hi p)]
  simp

end PairingEndpointEquiv
#print axioms PairingEndpointEquiv.equivalence
#print axioms PairingEndpointEquiv.card_eq
