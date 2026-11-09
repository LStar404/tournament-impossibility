import GlobalActivityFiniteRegroup
noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace StructuralActivitySeries
open PartialMatchingAffine StructuralPartialMatchingCounts PhysicalTiltedCovariance
variable {I S : Type*} [Fintype I] [Field S] [CharZero S] [Algebra ℚ S]

/-- Genuine finite sums of existing physical partial-matching weights. -/
def word {b : ℕ} (K A : I → I → S) (hK : ∀i j,K i j=K j i)
    (hA : ∀i j,A i j=A j i) (h : I → S) (d : Fin b →₀ ℕ)
    (a : Fin b → I) (j : ℕ) : PowerSeries S :=
  ∑p : PartialPairing (Positions d),if activityIndex d p=j then
    weight (covariance K A) (PhysicalPartialMatching.covariance_symmetry K A hK hA)
      (mean K A h) (fun x : Positions d => a x.1) p else 0

theorem word_coefficient {b : ℕ} (K A : I → I → S) (hK : ∀i j,K i j=K j i)
    (hA : ∀i j,A i j=A j i) (h : I → S) (d : Fin b →₀ ℕ)
    (hd : ∀v,3 ≤ d v) (a : Fin b → I) (j k : ℕ) :
    (word K A hK hA h d a j).coeff k=OrderedResidualActivities.activity K A hK hA h d a k j := by
  unfold word OrderedResidualActivities.activity
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hj : activityIndex d p=j
  · by_cases hk : j+b ≤ k
    · simp [hj,hk]
    · have hz := PhysicalActivityOrder.below K A hK hA h d hd a p k (by omega)
      simp [hj,hk,hz]
  · simp [hj]

def degree (K A : I → I → S) (hK : ∀i j,K i j=K j i)
    (hA : ∀i j,A i j=A j i) (h : I → S) (m j : ℕ) : PowerSeries S :=
  ∑b∈Finset.range (m/3+1),∑a : Fin b → I,
    ∑d∈Finset.finsuppAntidiag (Finset.univ : Finset (Fin b)) m,
      if ∀v,3 ≤ d v then PowerSeries.C (OrderedResidualPolynomial.scalar (S:=S) d)*word K A hK hA h d a j else 0

theorem degree_coefficient (K A : I → I → S) (hK : ∀i j,K i j=K j i)
    (hA : ∀i j,A i j=A j i) (h : I → S) (m j k : ℕ) :
    (degree K A hK hA h m j).coeff k=GlobalActivityFiniteRegroup.byIndex K A hK hA h m k j := by
  unfold degree GlobalActivityFiniteRegroup.byIndex
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro d hd
  split_ifs with hdeg
  · rw [PowerSeries.coeff_C_mul,word_coefficient K A hK hA h d hdeg]
  · simp
end StructuralActivitySeries
#print axioms StructuralActivitySeries.degree_coefficient
