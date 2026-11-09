import GlobalLogFiniteVertices

noncomputable section
namespace GlobalLogDegreeAssignments
open GlobalResidualLog
variable {I S P : Type*} [Fintype I] [Field S] [CharZero S] [Algebra ℚ S]
    [CommRing P] [Algebra S P] [Algebra ℚ P]

theorem local_coefficient (a : P) (d : ℕ) :
    (localLog (S:=S) a).coeff d =
      algebraMap S P ((ResidualLogarithm.logarithm (S:=S)).coeff d)*a^d := by
  simp only [localLog,PowerSeries.coeff_rescale,PowerSeries.coeff_map,mul_comm]

theorem ordered_degrees (a : I → P) (m : ℕ) :
    (∏i,FactorizedResidualIdentity.residual (S:=S) (a i)).coeff m =
      ∑b∈Finset.range (m/3+1),algebraMap ℚ P (1/(b.factorial:ℚ))*
        (∑label : Fin b → I, ∑d∈Finset.finsuppAntidiag (Finset.univ : Finset (Fin b)) m,
          ∏v : Fin b,algebraMap S P ((ResidualLogarithm.logarithm (S:=S)).coeff (d v)) *
            (a (label v))^(d v)) := by
  classical
  rw [GlobalLogFiniteVertices.ordered_vertices]
  apply Finset.sum_congr rfl
  intro b hb
  congr 1
  apply Finset.sum_congr rfl
  intro label hl
  rw [PowerSeries.coeff_prod]
  apply Finset.sum_congr rfl
  intro d hd
  exact Finset.prod_congr rfl (fun v hv => local_coefficient _ _)

theorem degree_small_zero (d : ℕ) (hd : d < 3) :
    (ResidualLogarithm.logarithm (S:=S)).coeff d=0 := by
  interval_cases d <;> simp [ResidualLogarithm.logarithm]

theorem assignment_zero {b : ℕ} (a : Fin b → P) (d : Fin b → ℕ)
    (h : ∃v,d v < 3) :
    (∏v : Fin b,algebraMap S P ((ResidualLogarithm.logarithm (S:=S)).coeff (d v))*a v^(d v))=0 := by
  classical
  obtain ⟨v,hv⟩ := h
  apply Finset.prod_eq_zero (Finset.mem_univ v)
  rw [degree_small_zero _ hv,map_zero,zero_mul]

theorem actual_ordered_degrees (m : ℕ) :
    (FactorizedResidualIdentity.actualResidual (I:=I) (S:=S)).coeff m =
      ∑b∈Finset.range (m/3+1),algebraMap ℚ (MvPolynomial I S) (1/(b.factorial:ℚ))*
        (∑label : Fin b → I, ∑d∈Finset.finsuppAntidiag (Finset.univ : Finset (Fin b)) m,
          ∏v : Fin b,algebraMap S (MvPolynomial I S)
            ((ResidualLogarithm.logarithm (S:=S)).coeff (d v)) *
            (MvPolynomial.X (label v))^(d v)) := by
  exact ordered_degrees (S:=S) (fun i : I => MvPolynomial.X i) m
end GlobalLogDegreeAssignments
#print axioms GlobalLogDegreeAssignments.actual_ordered_degrees
#print axioms GlobalLogDegreeAssignments.assignment_zero
