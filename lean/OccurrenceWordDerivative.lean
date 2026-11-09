import PolynomialTiltedRecurrence
import Mathlib.Algebra.BigOperators.Ring.List

noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace OccurrenceWordDerivative
variable {I S : Type*} [CommSemiring S]

def polynomial : List I → MvPolynomial I S
  | [] => 1
  | i::w => MvPolynomial.X i * polynomial w

/-- One entry per occurrence, even when the numerical labels coincide. -/
def deletions : List I → List (I × List I)
  | [] => []
  | i::w => (i,w) :: (deletions w).map (fun p => (p.1,i::p.2))

theorem deletion_length (w : List I) (p : I × List I) (hp : p ∈ deletions w) :
    p.2.length + 1 = w.length := by
  induction w generalizing p with
  | nil => simp [deletions] at hp
  | cons i w ih =>
    simp only [deletions,List.mem_cons,List.mem_map] at hp
    rcases hp with rfl | ⟨q,hq,rfl⟩
    · rfl
    · simp only [List.length_cons]
      have hh := ih q hq
      omega

theorem derivative (w : List I) (j : I) :
    MvPolynomial.pderiv j (polynomial (S:=S) w) =
      ((deletions w).map (fun p => if j=p.1 then polynomial p.2 else 0)).sum := by
  induction w with
  | nil => simp [polynomial,deletions]
  | cons i w ih =>
    simp only [polynomial,MvPolynomial.pderiv_mul,ih,deletions,List.map_cons,
      List.sum_cons,List.map_map,Function.comp_def]
    rw [MvPolynomial.pderiv_X]
    simp only [Pi.single_apply]
    rw [← List.sum_map_mul_left]
    congr 1
    · by_cases hh : j=i
      · subst j; simp
      · simp [hh,Ne.symm hh]
    · apply congrArg List.sum
      apply List.map_congr_left
      intro p hp
      split_ifs <;> simp

end OccurrenceWordDerivative
#print axioms OccurrenceWordDerivative.derivative
