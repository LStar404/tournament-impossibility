import ResidualSingleAssignment

noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace BipartiteResidualSecondZero
open ResidualSingleAssignment ResidualPhysicalAssignments ResidualFirstCoefficient
variable {I S : Type*} [Fintype I] [Field S] [CharZero S]

theorem moment_second_zero (K : I → I → S) (hs : ∀i j,K i j=K j i)
    (h : I → S) (A : I → I → S) (hA : ∀i j,A i j=A j i)
    (hdiag : ∀i,K i i=0) (m : ℕ) (hm : m=3 ∨ m=4) :
    (momentCoefficient K A h m).coeff 2=0 := by
  simp only [momentCoefficient,map_sum,PowerSeries.coeff_C_mul]
  apply Finset.sum_eq_zero
  intro d hd
  by_cases hw : (∏i : I,ResidualDegreeAssignments.scalarCoefficient (S:=S) (d i))=0
  · rw [hw,zero_mul]
  obtain ⟨i,he⟩ := single_assignment m (by omega) d hd hw
  rw [he,single_moment K hs h A hA]
  rcases hm with rfl | rfl
  · have hh := PhysicalCovarianceInitial.third_second_zero K A h i (hdiag i)
    simpa only [List.replicate_succ,List.replicate_zero,mul_zero] using congrArg
      (fun x : S => (∏j : I,ResidualDegreeAssignments.scalarCoefficient (S:=S) ((Finsupp.single i 3) j))*x) hh
  · have hh := PhysicalCovarianceInitial.fourth_second_zero K A h i (hdiag i)
    simpa only [List.replicate_succ,List.replicate_zero,mul_zero] using congrArg
      (fun x : S => (∏j : I,ResidualDegreeAssignments.scalarCoefficient (S:=S) ((Finsupp.single i 4) j))*x) hh

theorem block_diagonal {n : ℕ} (M : Matrix (Fin n) (Fin n) S) (i : Fin n ⊕ Fin n) :
    FullWickSquarefreeCompatibility.block M i i=0 := by cases i <;> rfl

theorem actual_second_zero {n : ℕ} [Algebra ℚ S] (M : Matrix (Fin n) (Fin n) S) :
    (ActualResidualFrozenFactorization.residualZ M).coeff 2=0 := by
  rw [actual_coefficient]
  have h3 := moment_second_zero (FullWickSquarefreeCompatibility.block M)
    (FullWickSquarefreeCompatibility.block_symm M) (fun _ => 1)
    (RawFormalMixedSpecialization.identityInteraction (I:=Fin n ⊕ Fin n) (S:=S))
    ActualResidualFrozenFactorization.identity_symmetry (block_diagonal M) 3 (Or.inl rfl)
  have h4 := moment_second_zero (FullWickSquarefreeCompatibility.block M)
    (FullWickSquarefreeCompatibility.block_symm M) (fun _ => 1)
    (RawFormalMixedSpecialization.identityInteraction (I:=Fin n ⊕ Fin n) (S:=S))
    ActualResidualFrozenFactorization.identity_symmetry (block_diagonal M) 4 (Or.inr rfl)
  norm_num [Finset.sum_range_succ,moment_zero,moment_small _ _ _ 1 (by omega),
    moment_small _ _ _ 2 (by omega),h3,h4]

/-- Concrete agreement of the true finite polynomial with its actual core
through degree two; no bound on higher coefficients is asserted. -/
theorem low_frozen_core_match {n : ℕ} [Algebra ℚ S] (M : Matrix (Fin n) (Fin n) S)
    (k : ℕ) (hk : k ≤ 2) :
    ((FrozenPartialPairingPolynomial.frozenPolynomial M : PowerSeries S)).coeff k =
      (ActualResidualFrozenFactorization.core M).coeff k := by
  rw [ActualResidualFrozenFactorization.polynomial_factorization]
  interval_cases k <;>
    norm_num [PowerSeries.coeff_mul,Finset.Nat.antidiagonal_succ,actual_constant,
      actual_first_zero,actual_second_zero]

end BipartiteResidualSecondZero
#print axioms BipartiteResidualSecondZero.actual_second_zero

#print axioms BipartiteResidualSecondZero.low_frozen_core_match
