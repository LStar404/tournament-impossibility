import PartialMatchingWeightOrder

noncomputable section
namespace PhysicalActivityOrder
open PartialMatchingAffine StructuralPartialMatchingCounts PhysicalTiltedCovariance
variable {I S : Type*} [Fintype I] [Field S] [CharZero S]

theorem divisible {b : ℕ} (K A : I → I → S) (hK : ∀i j,K i j=K j i)
    (hA : ∀i j,A i j=A j i) (h : I → S) (d : Fin b → ℕ) (hd : ∀v,3 ≤ d v)
    (a : Fin b → I) (p : PartialPairing (Positions d)) :
    (PowerSeries.X : PowerSeries S)^(activityIndex d p+b) ∣
      weight (covariance K A) (PhysicalPartialMatching.covariance_symmetry K A hK hA)
        (mean K A h) (fun x => a x.1) p := by
  rw [← (structural_bounds d hd p).2.2]
  exact PartialMatchingWeightOrder.divisible _ _ _ _ _
    (covariance_constant K A) (mean_constant K A h)

theorem below {b : ℕ} (K A : I → I → S) (hK : ∀i j,K i j=K j i)
    (hA : ∀i j,A i j=A j i) (h : I → S) (d : Fin b → ℕ) (hd : ∀v,3 ≤ d v)
    (a : Fin b → I) (p : PartialPairing (Positions d)) (k : ℕ)
    (hk : k < activityIndex d p+b) :
    (weight (covariance K A) (PhysicalPartialMatching.covariance_symmetry K A hK hA)
      (mean K A h) (fun x => a x.1) p).coeff k=0 := by
  obtain ⟨F,hF⟩ := divisible K A hK hA h d hd a p
  rw [hF,PowerSeries.coeff_X_pow_mul']
  simp [show ¬activityIndex d p+b ≤ k by omega]
end PhysicalActivityOrder
#print axioms PhysicalActivityOrder.below
