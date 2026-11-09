import ResidualDegreeAssignments
import ActualResidualFrozenFactorization

noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace ResidualPhysicalAssignments
open ResidualDegreeAssignments PhysicalWordRecurrence PolynomialTiltedRecurrence
variable {I S : Type*} [Fintype I] [Field S] [CharZero S]

def momentCoefficient (K A : I → I → S) (h : I → S) (m : ℕ) : PowerSeries S :=
  ∑d∈Finset.finsuppAntidiag Finset.univ m,PowerSeries.C (∏i : I,scalarCoefficient (S:=S) (d i))*
    PhysicalWordEvenDescent.moment K A h (word d)

theorem tilted_smul (K : I → I → S) (hs : ∀i j,K i j=K j i)
    (h : I → S) (A : I → I → S) (a : S) (R : MvPolynomial I S) :
    tilted K hs h A (a • R)=PowerSeries.C a*tilted K hs h A R := by
  unfold tilted PolynomialInsertionWard.inserted
  rw [FormalWickInsertion.moment_smul_insert,mul_assoc]

theorem shifted_insertion (K : I → I → S) (hs : ∀i j,K i j=K j i)
    (h : I → S) (A : I → I → S) (m : ℕ) :
    PowerSeries.X^m*tilted K hs h A ((FactorizedResidualIdentity.actualResidual (I:=I) (S:=S)).coeff m)=
      ∑d∈Finset.finsuppAntidiag Finset.univ m,PowerSeries.C (∏i : I,scalarCoefficient (S:=S) (d i))*
        physical K hs h A (word d) := by
  rw [residual_coefficient]
  change PowerSeries.X^m*(tiltedAdd K hs h A) _ = _
  rw [map_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  change PowerSeries.X^m*tilted K hs h A _ = _
  rw [tilted_smul,physical,length_assignment d m hd]
  ring

theorem expansion (K : I → I → S) (hs : ∀i j,K i j=K j i)
    (h : I → S) (A : I → I → S) (hA : ∀i j,A i j=A j i) (m : ℕ) :
    PowerSeries.expand 2 (by decide) (momentCoefficient K A h m)=
      PowerSeries.X^m*tilted K hs h A ((FactorizedResidualIdentity.actualResidual (I:=I) (S:=S)).coeff m) := by
  rw [momentCoefficient,map_sum,shifted_insertion]
  apply Finset.sum_congr rfl
  intro d hd
  rw [map_mul,PowerSeries.expand_C,PhysicalWordEvenDescent.expand_moment K hs h A hA]

theorem below_order (K : I → I → S) (hs : ∀i j,K i j=K j i)
    (h : I → S) (A : I → I → S) (hA : ∀i j,A i j=A j i)
    (m k : ℕ) (hk : 2*k < m) : (momentCoefficient K A h m).coeff k=0 := by
  simp only [momentCoefficient,map_sum,PowerSeries.coeff_C_mul]
  apply Finset.sum_eq_zero
  intro d hd
  rw [PhysicalWordCoefficientOrder.coefficient_below_order K hs h A hA (word d) k
    (by rw [length_assignment d m hd]; exact hk),mul_zero]

theorem coefficient_shift (K : I → I → S) (hs : ∀i j,K i j=K j i)
    (h : I → S) (A : I → I → S) (hA : ∀i j,A i j=A j i)
    (m k : ℕ) (hm : m ≤ 2*k) :
    (momentCoefficient K A h m).coeff k =
      (tilted K hs h A ((FactorizedResidualIdentity.actualResidual (I:=I) (S:=S)).coeff m)).coeff (2*k-m) := by
  have hh := congrArg (fun F : PowerSeries S => F.coeff (2*k)) (expansion K hs h A hA m)
  simpa only [PowerSeries.coeff_expand_mul,PowerSeries.coeff_X_pow_mul',if_pos hm] using hh

/-- The actual residual has a locally finite W/eta moment formula at every degree. -/
theorem actual_coefficient {n : ℕ} [Algebra ℚ S] (M : Matrix (Fin n) (Fin n) S) (k : ℕ) :
    (ActualResidualFrozenFactorization.residualZ M).coeff k =
      ∑m∈Finset.range (2*k+1),
        (momentCoefficient (FullWickSquarefreeCompatibility.block M)
          (RawFormalMixedSpecialization.identityInteraction (I:=Fin n ⊕ Fin n) (S:=S))
          (fun _ => 1) m).coeff k := by
  rw [ActualResidualFrozenFactorization.residual_coefficient]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro m hm
  symm
  exact coefficient_shift (FullWickSquarefreeCompatibility.block M)
    (FullWickSquarefreeCompatibility.block_symm M) (fun _ => 1) _
    ActualResidualFrozenFactorization.identity_symmetry m k (by have hh := Finset.mem_range.mp hm; omega)

end ResidualPhysicalAssignments
#print axioms ResidualPhysicalAssignments.expansion
#print axioms ResidualPhysicalAssignments.below_order

#print axioms ResidualPhysicalAssignments.actual_coefficient
