import ActualFiniteActivity
noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace ActivityZeroNormalization
open StructuralPartialMatchingCounts
variable {I S : Type*} [Fintype I] [Field S] [CharZero S] [Algebra ℚ S]

theorem empty_word (K A : I → I → S) (hK : ∀i j,K i j=K j i)
    (hA : ∀i j,A i j=A j i) (h : I → S) (d : Fin 0 →₀ ℕ) (a : Fin 0 → I) :
    StructuralActivitySeries.word K A hK hA h d a 0=1 := by
  have hj (p : PartialMatchingAffine.PartialPairing (Positions d)) : activityIndex d p=0 := by
    have ht := total_degree d p
    simp only [Finset.univ_eq_empty,Finset.sum_empty] at ht
    unfold activityIndex
    omega
  unfold StructuralActivitySeries.word
  simp only [hj,ite_true]
  change PartialMatchingAffine.total _ _ _ _=1
  rw [← OrderedVertexWord.physical_matching K A hK hA h d a]
  have hw : OrderedVertexWord.word d a=[] := by
    apply List.eq_nil_of_length_eq_zero
    rw [OrderedVertexWord.length]
    simp
  rw [hw,PhysicalWordEvenDescent.moment_nil]

theorem zero (K A : I → I → S) (hK : ∀i j,K i j=K j i)
    (hA : ∀i j,A i j=A j i) (h : I → S) :
    ActualFiniteActivity.series K A hK hA h 0=1 := by
  simp only [ActualFiniteActivity.series,Nat.mul_zero,zero_add,Finset.sum_range_one]
  simp only [StructuralActivitySeries.degree,Nat.zero_div,zero_add,Finset.sum_range_one]
  simp [empty_word,OrderedResidualPolynomial.scalar]
end ActivityZeroNormalization
#print axioms ActivityZeroNormalization.zero
