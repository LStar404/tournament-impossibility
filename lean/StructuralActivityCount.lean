import PartialMatchingFiberCount
noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace StructuralActivityCount
open PartialMatchingAffine StructuralPartialMatchingCounts

abbrev Fiber {b : ℕ} (d : Fin b → ℕ) (j : ℕ) :=
  {p : PartialPairing (Positions d) // activityIndex d p=j}

theorem counts {b : ℕ} (d : Fin b → ℕ) (hd : ∀v,3 ≤ d v)
    (D e h j : ℕ) (hD : (∑v,d v)=D) (hde : D=2*e+h) (hj : e+h=j+b)
    (p : PartialPairing (Positions d)) :
    activityIndex d p=j ↔ pairCount p=e := by
  have htotal := total_degree d p
  have hstruct := (structural_bounds d hd p).2.2
  omega

def fiberEquiv {b : ℕ} (d : Fin b → ℕ) (hd : ∀v,3 ≤ d v)
    (D e h j : ℕ) (hD : (∑v,d v)=D) (hde : D=2*e+h) (hj : e+h=j+b) :
    Fiber d j ≃ PartialMatchingFiberCount.Fiber (Positions d) e :=
  Equiv.subtypeEquivRight (counts d hd D e h j hD hde hj)

theorem count {b : ℕ} (d : Fin b → ℕ) (hd : ∀v,3 ≤ d v)
    (D e h j : ℕ) (hD : (∑v,d v)=D) (hde : D=2*e+h) (hj : e+h=j+b) :
    Fintype.card (Fiber d j)=D.choose (2*e)*ConstantPairingMoments.pairFactor e := by
  rw [Fintype.card_congr (fiberEquiv d hd D e h j hD hde hj),PartialMatchingFiberCount.fiber_count]
  have hc : Fintype.card (Positions d)=D := by simpa [Fintype.card_sigma] using hD
  rw [hc]

theorem bound {b : ℕ} (d : Fin b → ℕ) (hd : ∀v,3 ≤ d v)
    (D e h j : ℕ) (hD : (∑v,d v)=D) (hde : D=2*e+h) (hj : e+h=j+b) :
    Fintype.card (Fiber d j) ≤ 2^D*D^e := by
  rw [count d hd D e h j hD hde hj]
  exact Nat.mul_le_mul (Nat.choose_le_two_pow _ _) (PartialMatchingFiberCount.pairFactor_bound D e (by omega))
end StructuralActivityCount
#print axioms StructuralActivityCount.count
