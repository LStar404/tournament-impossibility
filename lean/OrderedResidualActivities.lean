import PartialMatchingActivityGrouping

noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace OrderedResidualActivities
open PartialMatchingAffine StructuralPartialMatchingCounts PhysicalTiltedCovariance OrderedResidualPolynomial
variable {I S : Type*} [Fintype I] [Field S] [CharZero S] [Algebra ℚ S]

def activity {b : ℕ} (K A : I → I → S) (hK : ∀i j,K i j=K j i)
    (hA : ∀i j,A i j=A j i) (h : I → S) (d : Fin b →₀ ℕ)
    (a : Fin b → I) (k j : ℕ) : S :=
  ∑p : PartialPairing (Positions d), if activityIndex d p=j ∧ j+b ≤ k then
    (weight (covariance K A) (PhysicalPartialMatching.covariance_symmetry K A hK hA)
      (mean K A h) (fun x : Positions d => a x.1) p).coeff k else 0

theorem scalar_zero {b : ℕ} (d : Fin b →₀ ℕ) (hd : ¬∀v,3 ≤ d v) : scalar (S:=S) d=0 := by
  classical
  push_neg at hd
  obtain ⟨v,hv⟩ := hd
  unfold scalar
  have hz : (∏v : Fin b,(ResidualLogarithm.logarithm (S:=S)).coeff (d v))=0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ v)
    exact GlobalLogDegreeAssignments.degree_small_zero _ hv
  rw [hz,mul_zero]

theorem weighted_word {b : ℕ} (K A : I → I → S) (hK : ∀i j,K i j=K j i)
    (hA : ∀i j,A i j=A j i) (h : I → S) (d : Fin b →₀ ℕ)
    (a : Fin b → I) (k : ℕ) :
    scalar (S:=S) d*(PhysicalWordEvenDescent.moment K A h (OrderedVertexWord.word d a)).coeff k=
      if ∀v,3 ≤ d v then scalar (S:=S) d*∑j∈Finset.range (k+1),activity K A hK hA h d a k j else 0 := by
  classical
  split_ifs with hd
  · rw [OrderedVertexWord.physical_matching K A hK hA h,
      PartialMatchingActivityGrouping.grouped K A hK hA h d hd a]
    rfl
  · rw [scalar_zero d hd,zero_mul]

def groupedCoefficient (K A : I → I → S) (hK : ∀i j,K i j=K j i)
    (hA : ∀i j,A i j=A j i) (h : I → S) (m k : ℕ) : S :=
  ∑b∈Finset.range (m/3+1),∑a : Fin b → I,
    ∑d∈Finset.finsuppAntidiag (Finset.univ : Finset (Fin b)) m,
      if ∀v,3 ≤ d v then scalar (S:=S) d*∑j∈Finset.range (k+1),activity K A hK hA h d a k j else 0

theorem coefficient (K A : I → I → S) (hK : ∀i j,K i j=K j i)
    (hA : ∀i j,A i j=A j i) (h : I → S) (m k : ℕ) :
    (ResidualPhysicalAssignments.momentCoefficient K A h m).coeff k=
      groupedCoefficient K A hK hA h m k := by
  rw [← OrderedResidualTilted.eq_old K A hK hA h m]
  unfold OrderedResidualTilted.momentCoefficient groupedCoefficient
  simp only [map_sum,PowerSeries.coeff_C_mul]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro d hd
  exact weighted_word K A hK hA h d a k

/-- Actual residual coefficients, not a definition of an auxiliary desired residual. -/
theorem actual_coefficient {n : ℕ} (M : Matrix (Fin n) (Fin n) S) (k : ℕ) :
    (ActualResidualFrozenFactorization.residualZ M).coeff k=
      ∑m∈Finset.range (2*k+1), groupedCoefficient (FullWickSquarefreeCompatibility.block M)
        RawFormalMixedSpecialization.identityInteraction (FullWickSquarefreeCompatibility.block_symm M)
        ActualResidualFrozenFactorization.identity_symmetry (fun _ => 1) m k := by
  rw [ResidualPhysicalAssignments.actual_coefficient]
  apply Finset.sum_congr rfl
  intro m hm
  exact coefficient _ _ _ _ _ m k
end OrderedResidualActivities
#print axioms OrderedResidualActivities.actual_coefficient
