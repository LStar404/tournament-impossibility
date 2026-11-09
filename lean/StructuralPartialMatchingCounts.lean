import PartialMatchingInvolution

noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace StructuralPartialMatchingCounts
open PartialMatchingAffine
variable {V : Type*} [Fintype V]

def pairCount (p : PartialPairing V) : ℕ := p.1.card/2
def singletonCount (p : PartialPairing V) : ℕ := (Finset.univ \ p.1).card

theorem paired_even (p : PartialPairing V) : Even p.1.card := by
  simpa using PairingMomentParity.pairing_even p.2

theorem occurrence_count (p : PartialPairing V) :
    Fintype.card V=2*pairCount p+singletonCount p := by
  have hd : 2 ∣ p.1.card := even_iff_two_dvd.mp (paired_even p)
  have hh : 2*(p.1.card/2)=p.1.card := Nat.mul_div_cancel' hd
  have hs := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ p.1)
  simp only [Finset.card_univ] at hs
  dsimp [pairCount,singletonCount]
  omega

abbrev Positions {b : ℕ} (d : Fin b → ℕ) := Σv : Fin b,Fin (d v)

def activityIndex {b : ℕ} (d : Fin b → ℕ) (p : PartialPairing (Positions d)) : ℕ :=
  pairCount p+singletonCount p-b

theorem total_degree {b : ℕ} (d : Fin b → ℕ) (p : PartialPairing (Positions d)) :
    (∑v,d v)=2*pairCount p+singletonCount p := by
  simpa [Fintype.card_sigma] using occurrence_count p

theorem structural_bounds {b : ℕ} (d : Fin b → ℕ) (hd : ∀v,3 ≤ d v)
    (p : PartialPairing (Positions d)) :
    b ≤ 2*activityIndex d p ∧
    (∑v,d v) ≤ 6*activityIndex d p ∧
    pairCount p+singletonCount p=activityIndex d p+b := by
  have hlo : 3*b ≤ ∑v,d v := by
    calc
      3*b = ∑v : Fin b,3 := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun v hv => hd v)
  have he := total_degree d p
  have hb : b ≤ pairCount p+singletonCount p := by omega
  have hj : activityIndex d p+b=pairCount p+singletonCount p := by
    exact Nat.sub_add_cancel hb
  constructor
  · omega
  constructor <;> omega

theorem positive_degree_bound {b : ℕ} (d : Fin b → ℕ) (hd : ∀v,3 ≤ d v)
    (p : PartialPairing (Positions d)) (hb : 0 < b) :
    activityIndex d p+1 ≤ pairCount p+singletonCount p := by
  have hh := (structural_bounds d hd p).2.2
  omega

end StructuralPartialMatchingCounts
#print axioms StructuralPartialMatchingCounts.structural_bounds
