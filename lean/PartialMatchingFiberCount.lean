import StructuralPartialMatchingCounts
import ConstantPairingCount
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Bounds

noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace PartialMatchingFiberCount
open PartialMatchingAffine StructuralPartialMatchingCounts FinitePairingTransport

variable {V : Type*} [Fintype V]

abbrev Fiber (V : Type*) [Fintype V] (e : ℕ) :=
  {p : PartialPairing V // pairCount p=e}

theorem pairCount_iff (p : PartialPairing V) (e : ℕ) :
    pairCount p=e ↔ p.1.card=2*e := by
  have hd := even_iff_two_dvd.mp (paired_even p)
  have hh := Nat.mul_div_cancel' hd
  dsimp [pairCount]
  omega

def fiberEquiv (e : ℕ) : Fiber V e ≃
    Σs : {s : Finset V // s.card=2*e},Pairing s.val where
  toFun p := ⟨⟨p.val.1,(pairCount_iff p.val e).mp p.property⟩,p.val.2⟩
  invFun p := ⟨⟨p.1.val,p.2⟩,(pairCount_iff ⟨p.1.val,p.2⟩ e).mpr p.1.property⟩
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl

theorem subset_count (e : ℕ) :
    Fintype.card {s : Finset V // s.card=2*e}=(Fintype.card V).choose (2*e) := by
  rw [Fintype.card_of_subtype ((Finset.univ : Finset V).powersetCard (2*e))
    (by intro s; simp),Finset.card_powersetCard,Finset.card_univ]

theorem pairing_count (s : Finset V) (e : ℕ) (hs : s.card=2*e) :
    Fintype.card (Pairing s)=ConstantPairingMoments.pairFactor e := by
  let f : s ≃ Fin (2*e) := Fintype.equivOfCardEq (by simpa using hs)
  rw [Fintype.card_congr (transportEquiv f)]
  exact ConstantPairingCount.actual_pairing_count e

/-- Exact count of actual occurrence-position partial pairings, not edge lists. -/
theorem fiber_count (e : ℕ) :
    Fintype.card (Fiber V e)=(Fintype.card V).choose (2*e)*ConstantPairingMoments.pairFactor e := by
  rw [Fintype.card_congr (fiberEquiv (V:=V) e),Fintype.card_sigma]
  have hc (s : {s : Finset V // s.card=2*e}) :
      Fintype.card (Pairing s.val)=ConstantPairingMoments.pairFactor e := pairing_count s.val e s.property
  simp_rw [hc]
  simp [subset_count]

theorem pairFactor_bound (D e : ℕ) (h : 2*e ≤ D) :
    ConstantPairingMoments.pairFactor e ≤ D^e := by
  unfold ConstantPairingMoments.pairFactor
  calc
    _ ≤ ∏i∈Finset.range e,D := Finset.prod_le_prod (fun i hi => by
      have hi' := Finset.mem_range.mp hi
      omega)
    _ = D^e := by simp

theorem fiber_bound (e : ℕ) (he : 2*e ≤ Fintype.card V) :
    Fintype.card (Fiber V e) ≤ 2^(Fintype.card V)*(Fintype.card V)^e := by
  rw [fiber_count]
  exact Nat.mul_le_mul (Nat.choose_le_two_pow _ _) (pairFactor_bound _ e he)
end PartialMatchingFiberCount
#print axioms PartialMatchingFiberCount.fiber_count
#print axioms PartialMatchingFiberCount.fiber_bound
