import OrderedResidualActivities

noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace GlobalActivityFiniteRegroup
open OrderedResidualActivities OrderedResidualPolynomial StructuralPartialMatchingCounts
variable {I S : Type*} [Fintype I] [Field S] [CharZero S] [Algebra ℚ S]

def byIndex (K A : I → I → S) (hK : ∀i j,K i j=K j i)
    (hA : ∀i j,A i j=A j i) (h : I → S) (m k j : ℕ) : S :=
  ∑b∈Finset.range (m/3+1),∑a : Fin b → I,
    ∑d∈Finset.finsuppAntidiag (Finset.univ : Finset (Fin b)) m,
      if ∀v,3 ≤ d v then scalar (S:=S) d*activity K A hK hA h d a k j else 0

theorem regroup (K A : I → I → S) (hK : ∀i j,K i j=K j i)
    (hA : ∀i j,A i j=A j i) (h : I → S) (m k : ℕ) :
    groupedCoefficient K A hK hA h m k=∑j∈Finset.range (k+1),byIndex K A hK hA h m k j := by
  classical
  unfold groupedCoefficient byIndex
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  split_ifs with hdeg
  · simp only [if_pos hdeg,Finset.mul_sum]
  · simp [hdeg]

theorem activity_constraints {b : ℕ} (K A : I → I → S) (hK : ∀i j,K i j=K j i)
    (hA : ∀i j,A i j=A j i) (h : I → S) (d : Fin b →₀ ℕ)
    (hd : ∀v,3 ≤ d v) (a : Fin b → I) (m k j : ℕ)
    (hm : (∑v,d v)=m) (bad : ¬(b ≤ 2*j ∧ m ≤ 6*j ∧ j+b ≤ k)) :
    activity K A hK hA h d a k j=0 := by
  classical
  unfold activity
  apply Finset.sum_eq_zero
  intro p hp
  split_ifs with hj
  · have hb := structural_bounds d hd p
    exact False.elim (bad ⟨by simpa [hj.1] using hb.1,
      by simpa [hj.1,hm] using hb.2.1,hj.2⟩)
  · rfl

/-- Global finite j regroup of the true residual coefficient; j is not k. -/
theorem actual_regroup {n : ℕ} (M : Matrix (Fin n) (Fin n) S) (k : ℕ) :
    (ActualResidualFrozenFactorization.residualZ M).coeff k=
      ∑j∈Finset.range (k+1),∑m∈Finset.range (2*k+1),
        byIndex (FullWickSquarefreeCompatibility.block M) RawFormalMixedSpecialization.identityInteraction
          (FullWickSquarefreeCompatibility.block_symm M) ActualResidualFrozenFactorization.identity_symmetry
          (fun _ => 1) m k j := by
  rw [OrderedResidualActivities.actual_coefficient]
  simp only [regroup]
  exact Finset.sum_comm
end GlobalActivityFiniteRegroup
#print axioms GlobalActivityFiniteRegroup.actual_regroup
#print axioms GlobalActivityFiniteRegroup.activity_constraints
