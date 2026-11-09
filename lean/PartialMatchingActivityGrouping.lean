import OrderedResidualTilted

noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace PartialMatchingActivityGrouping
open PartialMatchingAffine StructuralPartialMatchingCounts PhysicalTiltedCovariance
variable {I S : Type*} [Fintype I] [Field S] [CharZero S]

theorem grouped {b : ℕ} (K A : I → I → S) (hK : ∀i j,K i j=K j i)
    (hA : ∀i j,A i j=A j i) (h : I → S) (d : Fin b → ℕ)
    (hd : ∀v,3 ≤ d v) (a : Fin b → I) (k : ℕ) :
    (total (covariance K A) (PhysicalPartialMatching.covariance_symmetry K A hK hA)
      (mean K A h) (fun x : Positions d => a x.1)).coeff k =
      ∑j∈Finset.range (k+1),∑p : PartialPairing (Positions d),
        if activityIndex d p=j ∧ j+b ≤ k then
          (weight (covariance K A) (PhysicalPartialMatching.covariance_symmetry K A hK hA)
            (mean K A h) (fun x : Positions d => a x.1) p).coeff k else 0 := by
  classical
  unfold PartialMatchingAffine.total
  rw [map_sum,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hj : activityIndex d p+b ≤ k
  · have hmem : activityIndex d p∈Finset.range (k+1) := by simp; omega
    rw [Finset.sum_eq_single (activityIndex d p)]
    · simp [hj]
    · intro j hj' hne
      simp [Ne.symm hne]
    · exact fun hn => False.elim (hn hmem)
  · rw [PhysicalActivityOrder.below K A hK hA h d hd a p k (by omega)]
    symm
    apply Finset.sum_eq_zero
    intro j hj'
    split_ifs with hh
    · exact False.elim (hj (by simpa [hh.1] using hh.2))
    · rfl
end PartialMatchingActivityGrouping
#print axioms PartialMatchingActivityGrouping.grouped
