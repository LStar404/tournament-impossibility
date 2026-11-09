import PhysicalPartialMatching
import ResidualPhysicalAssignments

noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace ResidualPartialMatchingExpansion
open ResidualPhysicalAssignments ResidualDegreeAssignments PhysicalTiltedCovariance
variable {I S : Type*} [Fintype I] [Field S] [CharZero S]

theorem moment_coefficient (K A : I → I → S) (hK : ∀i j,K i j=K j i)
    (hA : ∀i j,A i j=A j i) (h : I → S) (m : ℕ) :
    momentCoefficient K A h m =
      ∑d∈Finset.finsuppAntidiag Finset.univ m,PowerSeries.C (∏i : I,scalarCoefficient (S:=S) (d i))*
        PartialMatchingAffine.total (covariance K A) (PhysicalPartialMatching.covariance_symmetry K A hK hA)
          (mean K A h) (word d).get := by
  unfold momentCoefficient
  apply Finset.sum_congr rfl
  intro d hd
  rw [PhysicalPartialMatching.actual_matching K A hK hA]

/-- Actual residual coefficients as finite degree-assignment/partial-matching sums. -/
theorem actual_coefficient {n : ℕ} [Algebra ℚ S] (M : Matrix (Fin n) (Fin n) S) (k : ℕ) :
    (ActualResidualFrozenFactorization.residualZ M).coeff k =
      ∑m∈Finset.range (2*k+1),
        (∑d∈Finset.finsuppAntidiag Finset.univ m,
          PowerSeries.C (∏i : Fin n ⊕ Fin n,scalarCoefficient (S:=S) (d i))*
          PartialMatchingAffine.total
            (covariance (FullWickSquarefreeCompatibility.block M) RawFormalMixedSpecialization.identityInteraction)
            (PhysicalPartialMatching.covariance_symmetry _ _ (FullWickSquarefreeCompatibility.block_symm M)
              ActualResidualFrozenFactorization.identity_symmetry)
            (mean (FullWickSquarefreeCompatibility.block M) RawFormalMixedSpecialization.identityInteraction (fun _ => 1))
            (word d).get).coeff k := by
  rw [ResidualPhysicalAssignments.actual_coefficient]
  apply Finset.sum_congr rfl
  intro m hm
  rw [moment_coefficient _ _ (FullWickSquarefreeCompatibility.block_symm M)
    ActualResidualFrozenFactorization.identity_symmetry]
  congr 2
  ext d
  simp only [Finset.mem_finsuppAntidiag]

end ResidualPartialMatchingExpansion
#print axioms ResidualPartialMatchingExpansion.actual_coefficient
