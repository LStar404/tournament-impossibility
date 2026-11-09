import ResidualFirstCoefficient
import PhysicalCovarianceInitial

noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace ResidualSingleAssignment
open ResidualDegreeAssignments ResidualScalarActivities PhysicalWordCoefficientOrder
variable {I S : Type*} [Fintype I] [Field S] [CharZero S]

theorem single_assignment (m : ℕ) (hm : 0 < m ∧ m < 6) (d : I →₀ ℕ)
    (hd : d∈Finset.finsuppAntidiag Finset.univ m)
    (hw : (∏i : I,scalarCoefficient (S:=S) (d i)) ≠ 0) :
    ∃i,d=Finsupp.single i m := by
  have hc := active_coordinates_bound d m hd hw
  have hd0 : d≠0 := by
    intro hz; subst d
    have hh := (Finset.mem_finsuppAntidiag.mp hd).1
    simp at hh; omega
  have hcard : d.support.card=1 := by
    have hh : d.support.card≠0 := by
      intro he
      exact hd0 (Finsupp.support_eq_empty.mp (Finset.card_eq_zero.mp he))
    omega
  obtain ⟨i,hi⟩ := Finset.card_eq_one.mp hcard
  have hother (j : I) (hj : j≠i) : d j=0 := by
    apply Finsupp.notMem_support_iff.mp
    rw [hi]
    simpa using hj
  have hsum : ∑j : I,d j=d i := by
    apply Finset.sum_eq_single i
    · intro j hj hji; exact hother j hji
    · simp
  have hdi : d i=m := by rw [← hsum]; exact (Finset.mem_finsuppAntidiag.mp hd).1
  refine ⟨i,?_⟩
  ext j
  by_cases hj : j=i
  · subst j; simp [hdi]
  · simp [Finsupp.single_apply,hj,hother j hj]

theorem single_moment (K : I → I → S) (hs : ∀i j,K i j=K j i)
    (h : I → S) (A : I → I → S) (hA : ∀i j,A i j=A j i) (i : I) (m : ℕ) :
    PhysicalWordEvenDescent.moment K A h (word (Finsupp.single i m))=
      PhysicalWordEvenDescent.moment K A h (List.replicate m i) := by
  ext k
  rw [coefficient_identity K hs h A hA,coefficient_identity K hs h A hA]
  simp [PhysicalWordRecurrence.physical,length_word,polynomial_word,
    polynomial_replicate,Finsupp.single_apply]

end ResidualSingleAssignment
#print axioms ResidualSingleAssignment.single_assignment
#print axioms ResidualSingleAssignment.single_moment
