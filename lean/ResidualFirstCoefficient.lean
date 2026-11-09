import ResidualPhysicalAssignments
import ResidualScalarActivities

noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace ResidualFirstCoefficient
open ResidualPhysicalAssignments ResidualDegreeAssignments ResidualScalarActivities
variable {I S : Type*} [Fintype I] [Field S] [CharZero S]

theorem weight_zero_small (m : ℕ) (hm : 0 < m ∧ m < 3) (d : I →₀ ℕ)
    (hd : d∈Finset.finsuppAntidiag Finset.univ m) :
    (∏i : I,scalarCoefficient (S:=S) (d i))=0 := by
  by_contra hn
  have hh := active_coordinates_bound d m hd hn
  have hc : d.support.card=0 := by omega
  have hz : d=0 := Finsupp.support_eq_empty.mp (Finset.card_eq_zero.mp hc)
  subst d
  have he := (Finset.mem_finsuppAntidiag.mp hd).1
  simp at he
  omega

theorem moment_zero (K A : I → I → S) (h : I → S) : momentCoefficient K A h 0=1 := by
  have hw : word (0:I →₀ ℕ)=[] := List.length_eq_zero_iff.mp (by simp [length_word])
  simp [momentCoefficient,scalar_zero,hw,PhysicalWordEvenDescent.moment_nil]

theorem moment_small (K A : I → I → S) (h : I → S) (m : ℕ) (hm : 0 < m ∧ m < 3) :
    momentCoefficient K A h m=0 := by
  unfold momentCoefficient
  apply Finset.sum_eq_zero
  intro d hd
  rw [weight_zero_small m hm d hd,map_zero,zero_mul]

theorem actual_constant {n : ℕ} [Algebra ℚ S] (M : Matrix (Fin n) (Fin n) S) :
    (ActualResidualFrozenFactorization.residualZ M).coeff 0=1 := by
  rw [actual_coefficient]
  simp [moment_zero]

theorem actual_first_zero {n : ℕ} [Algebra ℚ S] (M : Matrix (Fin n) (Fin n) S) :
    (ActualResidualFrozenFactorization.residualZ M).coeff 1=0 := by
  rw [actual_coefficient]
  norm_num [Finset.sum_range_succ,moment_zero,moment_small _ _ _ 1 (by omega),
    moment_small _ _ _ 2 (by omega)]

end ResidualFirstCoefficient
#print axioms ResidualFirstCoefficient.actual_first_zero
