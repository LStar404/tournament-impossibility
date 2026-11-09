import ResidualHomogeneity
import PhysicalWordCoefficientOrder

noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace ResidualDegreeAssignments
open OccurrenceWordDerivative
variable {I S : Type*} [Fintype I] [Field S] [CharZero S]

def scalarCoefficient (m : ℕ) : S := (FactorizedResidualIdentity.residual (S:=S) (1:S)).coeff m

def word (d : I →₀ ℕ) : List I :=
  Finset.univ.toList.flatMap (fun i => List.replicate (d i) i)

theorem polynomial_append (u v : List I) :
    polynomial (S:=S) (u++v)=polynomial u*polynomial v := by
  induction u with
  | nil => simp [polynomial]
  | cons i u ih => simp [polynomial,ih,mul_assoc]

theorem polynomial_replicate (i : I) (m : ℕ) :
    polynomial (S:=S) (List.replicate m i)=(MvPolynomial.X i)^m := by
  induction m with
  | zero => simp [polynomial]
  | succ m ih => simp [List.replicate_succ,polynomial,ih,pow_succ,mul_comm]

theorem polynomial_word (d : I →₀ ℕ) :
    polynomial (S:=S) (word d)=∏i : I,(MvPolynomial.X i)^d i := by
  have hh (l : List I) : polynomial (S:=S) (l.flatMap (fun i => List.replicate (d i) i))=
      (l.map (fun i => (MvPolynomial.X i : MvPolynomial I S)^d i)).prod := by
    induction l with
    | nil => simp [polynomial]
    | cons i l ih => simp [polynomial_append,polynomial_replicate,ih]
  rw [word,hh,Finset.prod_map_toList]

theorem length_word (d : I →₀ ℕ) : (word d).length=∑i : I,d i := by
  simp [word,List.length_flatMap,Function.comp_def,Finset.sum_map_toList]

theorem length_assignment (d : I →₀ ℕ) (m : ℕ)
    (hd : d∈Finset.finsuppAntidiag Finset.univ m) : (word d).length=m := by
  rw [length_word]
  exact (Finset.mem_finsuppAntidiag.mp hd).1

/-- Actual finite product coefficient expansion, keeping every repeated occurrence. -/
theorem residual_coefficient (m : ℕ) :
    (FactorizedResidualIdentity.actualResidual (I:=I) (S:=S)).coeff m =
      ∑d∈Finset.finsuppAntidiag Finset.univ m,
        (∏i : I,scalarCoefficient (S:=S) (d i)) • polynomial (S:=S) (word d) := by
  unfold FactorizedResidualIdentity.actualResidual
  rw [PowerSeries.coeff_prod]
  apply Finset.sum_congr rfl
  intro d hd
  calc
    _ = ∏ i : I, scalarCoefficient (S:=S) (d i) • (MvPolynomial.X i : MvPolynomial I S)^d i := by
      apply Finset.prod_congr rfl
      intro i hi
      exact ResidualHomogeneity.coefficient (MvPolynomial.X i) (d i)
    _ = _ := by rw [Finset.prod_smul,← polynomial_word]

end ResidualDegreeAssignments
#print axioms ResidualDegreeAssignments.residual_coefficient
#print axioms ResidualDegreeAssignments.length_assignment
