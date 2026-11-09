import OrderedDegreeCompositionCount
import StructuralActivityWeighted
noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace ActualDegreeAssignmentCount

def assignments (D b : ℕ) : Finset (Fin b →₀ ℕ) :=
  (Finset.finsuppAntidiag (Finset.univ : Finset (Fin b)) D).filter (fun d => ∀i,3 ≤ d i)

def allAssignments (D : ℕ) : Finset (Σb : ℕ,Fin b →₀ ℕ) :=
  (Finset.range (D/3+1)).sigma (assignments D)

def toDegrees {D : ℕ} (p : {p // p∈allAssignments D}) : OrderedDegreeCompositionCount.Degrees D :=
  ⟨p.val.1,⟨fun i => p.val.2 i,
    (Finset.mem_filter.mp (Finset.mem_sigma.mp p.property).2).2,
    (Finset.mem_finsuppAntidiag.mp (Finset.mem_filter.mp (Finset.mem_sigma.mp p.property).2).1).1⟩⟩

def recover {D : ℕ} (p : OrderedDegreeCompositionCount.Degrees D) : Σb : ℕ,Fin b →₀ ℕ :=
  ⟨p.1,Finsupp.equivFunOnFinite.symm p.2.val⟩

theorem recover_toDegrees {D : ℕ} (p : {p // p∈allAssignments D}) : recover (toDegrees p)=p.val := by
  rcases p with ⟨⟨b,d⟩,hp⟩
  simp only [recover,toDegrees,Sigma.mk.inj_iff,heq_eq_eq,true_and]
  exact Finsupp.ext (fun i => rfl)

theorem injective (D : ℕ) : Function.Injective (@toDegrees D) := by
  intro p q h
  apply Subtype.ext
  simpa only [recover_toDegrees] using congrArg recover h

theorem count (D : ℕ) : (allAssignments D).card ≤ 2^(D-1) := by
  have hc := Fintype.card_le_of_injective _ (injective D)
  exact (by simpa using hc : (allAssignments D).card ≤ Fintype.card (OrderedDegreeCompositionCount.Degrees D)).trans
    (OrderedDegreeCompositionCount.degree_count D)

variable {I : Type*} [Fintype I]
/-- Reorder the actual degree contribution, without altering its multiplicities. -/
theorem degree_eq (K A : I → I → ℂ) (hK : ∀i j,K i j=K j i)
    (hA : ∀i j,A i j=A j i) (h : I → ℂ) (D j : ℕ) :
    StructuralActivitySeries.degree K A hK hA h D j=
      ∑p∈allAssignments D,StructuralActivityWeighted.labeled K A hK hA h p.2 j := by
  unfold StructuralActivitySeries.degree allAssignments
  rw [Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.sum_comm]
  unfold assignments StructuralActivityWeighted.labeled
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  split_ifs with hdeg
  · simp only [if_pos hdeg]
  · simp only [if_neg hdeg,Finset.sum_const_zero]
end ActualDegreeAssignmentCount
#print axioms ActualDegreeAssignmentCount.count
#print axioms ActualDegreeAssignmentCount.degree_eq
