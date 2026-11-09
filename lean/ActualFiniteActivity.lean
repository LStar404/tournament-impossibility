import StructuralActivitySeries
noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace ActualFiniteActivity
open StructuralActivitySeries StructuralPartialMatchingCounts
variable {I S : Type*} [Fintype I] [Field S] [CharZero S] [Algebra ℚ S]

theorem index_zero (K A : I → I → S) (hK : ∀i j,K i j=K j i)
    (hA : ∀i j,A i j=A j i) (h : I → S) (m k j : ℕ)
    (hm : 6*j < m ∨ 2*k < m) : GlobalActivityFiniteRegroup.byIndex K A hK hA h m k j=0 := by
  unfold GlobalActivityFiniteRegroup.byIndex
  apply Finset.sum_eq_zero
  intro b hb
  apply Finset.sum_eq_zero
  intro a ha
  apply Finset.sum_eq_zero
  intro d hd
  split_ifs with hdeg
  · have hsum := (Finset.mem_finsuppAntidiag.mp hd).1
    have hz : OrderedResidualActivities.activity K A hK hA h d a k j=0 := by
      unfold OrderedResidualActivities.activity
      apply Finset.sum_eq_zero
      intro p hp
      split_ifs with hpj
      · have hstruct := structural_bounds d hdeg p
        have htotal := total_degree d p
        have hsum' : (∑v : Fin b,d v)=m := hsum
        rw [hsum'] at htotal
        simp only [hsum'] at hstruct
        rcases hm with hm | hm <;> omega
      · rfl
    rw [hz,mul_zero]
  · rfl

/-- Finite structural activity, with the actual old weights and scalar coefficients. -/
def series (K A : I → I → S) (hK : ∀i j,K i j=K j i)
    (hA : ∀i j,A i j=A j i) (h : I → S) (j : ℕ) : PowerSeries S :=
  ∑m∈Finset.range (6*j+1),degree K A hK hA h m j

theorem coefficient (K A : I → I → S) (hK : ∀i j,K i j=K j i)
    (hA : ∀i j,A i j=A j i) (h : I → S) (j k : ℕ) :
    (series K A hK hA h j).coeff k=
      ∑m∈Finset.range (2*k+1),GlobalActivityFiniteRegroup.byIndex K A hK hA h m k j := by
  unfold series
  simp only [map_sum,degree_coefficient]
  by_cases hh : 6*j ≤ 2*k
  · apply Finset.sum_subset (Finset.range_mono (by omega))
    intro m hm hnot
    apply index_zero K A hK hA h m k j
    left
    simp only [Finset.mem_range] at hnot
    omega
  · symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro m hm hnot
    apply index_zero K A hK hA h m k j
    right
    simp only [Finset.mem_range] at hnot
    omega

/-- Coefficientwise recovery from real finite activities, not a new definition of residualZ. -/
theorem actual_residual {n : ℕ} (M : Matrix (Fin n) (Fin n) S) (k : ℕ) :
    (ActualResidualFrozenFactorization.residualZ M).coeff k=
      ∑j∈Finset.range (k+1),(series (FullWickSquarefreeCompatibility.block M)
        RawFormalMixedSpecialization.identityInteraction
        (FullWickSquarefreeCompatibility.block_symm M) ActualResidualFrozenFactorization.identity_symmetry
        (fun _ => 1) j).coeff k := by
  rw [GlobalActivityFiniteRegroup.actual_regroup]
  simp only [coefficient]
end ActualFiniteActivity
#print axioms ActualFiniteActivity.actual_residual
