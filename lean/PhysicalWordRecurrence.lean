import OccurrenceWordDerivative
import PhysicalTiltedCovariance

noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace PhysicalWordRecurrence
open OccurrenceWordDerivative PolynomialTiltedRecurrence
variable {I S : Type*} [Fintype I] [Field S] [CharZero S]

def tiltedAdd (K : I → I → S) (hs : ∀ i j,K i j=K j i)
    (h : I → S) (A : I → I → S) : MvPolynomial I S →+ PowerSeries S where
  toFun := tilted K hs h A
  map_zero' := by
    unfold tilted PolynomialInsertionWard.inserted
    have hz : FormalWickInsertion.moment K hs 0 (ActualMixedSourceWard.E h A)=0 := by
      ext n; simp
    rw [hz,zero_mul]
  map_add' P Q := by
    unfold tilted PolynomialInsertionWard.inserted
    have ha : FormalWickInsertion.moment K hs (P+Q) (ActualMixedSourceWard.E h A)=
        FormalWickInsertion.moment K hs P (ActualMixedSourceWard.E h A)+
        FormalWickInsertion.moment K hs Q (ActualMixedSourceWard.E h A) := by
      ext n; simp [add_mul]
    rw [ha,add_mul]

theorem contraction_sum (f : MvPolynomial I S →+ PowerSeries S)
    (V : I → PowerSeries S) (l : List (I × List I)) :
    (∑ j,V j * f ((l.map (fun p => if j=p.1 then polynomial p.2 else 0)).sum)) =
      (l.map (fun p => V p.1 * f (polynomial p.2))).sum := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.map_cons,List.sum_cons,map_add,mul_add,Finset.sum_add_distrib,ih]
    congr 1
    simp only [apply_ite,map_zero,mul_ite,mul_zero]
    simp

def physical (K : I → I → S) (hs : ∀ i j,K i j=K j i)
    (h : I → S) (A : I → I → S) (w : List I) : PowerSeries S :=
  PowerSeries.X^w.length * tilted K hs h A (polynomial w)

theorem physical_nil (K : I → I → S) (hs : ∀ i j,K i j=K j i)
    (h : I → S) (A : I → I → S) : physical K hs h A []=1 := by
  simp [physical,polynomial,tilted_one]

theorem recurrence (K : I → I → S) (hs : ∀ i j,K i j=K j i)
    (h : I → S) (A : I → I → S) (hA : ∀ i j,A i j=A j i)
    (i : I) (w : List I) :
    physical K hs h A (i::w) =
      PowerSeries.X^2 * MixedWardSolution.response K A h i * physical K hs h A w +
      ((deletions w).map (fun p => PowerSeries.X^2 * MixedWardSolution.covariance K A i p.1 *
        physical K hs h A p.2)).sum := by
  have hc := contraction_sum (tiltedAdd K hs h A) (MixedWardSolution.covariance K A i) (deletions w)
  simp only [← derivative] at hc
  change (∑ j, MixedWardSolution.covariance K A i j * tilted K hs h A (MvPolynomial.pderiv j (polynomial w))) = _ at hc
  unfold physical
  rw [polynomial,tilted_recurrence K hs h A hA,hc,mul_add,add_comm]
  congr 1
  · simp only [List.length_cons,pow_succ]; ring
  · rw [← List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro p hp
    have hl := deletion_length w p hp
    rw [List.length_cons,← hl]
    simp only [pow_succ, tiltedAdd, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    ring

end PhysicalWordRecurrence
#print axioms PhysicalWordRecurrence.recurrence
