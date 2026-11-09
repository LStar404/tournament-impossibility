import MixedWardSolution

noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace PolynomialInsertionWard
open FormalWickInsertion ActualMixedSourceWard ActualMixedWardMatrix
variable {I S : Type*} [Fintype I] [Field S] [CharZero S]

def inserted (K : I → I → S) (hs : ∀ i j, K i j=K j i)
    (h : I → S) (A : I → I → S) (R : MvPolynomial I S) := moment K hs R (E h A)

theorem ward (K : I → I → S) (hs : ∀ i j, K i j=K j i)
    (h : I → S) (A : I → I → S) (hA : ∀ i j, A i j=A j i)
    (R : MvPolynomial I S) (i : I) :
    inserted K hs h A (MvPolynomial.X i*R) =
      ∑ j, PowerSeries.C (K i j) * (inserted K hs h A (MvPolynomial.pderiv j R) +
        PowerSeries.X*(PowerSeries.C (h j)*inserted K hs h A R) -
        PowerSeries.X^2*∑ l,PowerSeries.C (A j l)*inserted K hs h A (MvPolynomial.X l*R)) := by
  unfold inserted
  rw [ibp]
  apply Finset.sum_congr rfl
  intro j hj
  rw [inserted_derivative K hs h A hA]
  have hc (l : I) : R*MvPolynomial.X l=MvPolynomial.X l*R := mul_comm _ _
  simp only [hc]
  ring

theorem system (K : I → I → S) (hs : ∀ i j, K i j=K j i)
    (h : I → S) (A : I → I → S) (hA : ∀ i j, A i j=A j i)
    (R : MvPolynomial I S) (i : I) :
    (block K A).mulVec (fun l => inserted K hs h A (MvPolynomial.X l*R)) i =
      ∑ j,PowerSeries.C (K i j)*inserted K hs h A (MvPolynomial.pderiv j R) +
        PowerSeries.X*(∑ j,PowerSeries.C (K i j)*PowerSeries.C (h j))*inserted K hs h A R := by
  rw [block_mulVec,ward K hs h A hA]
  simp only [mul_sub,mul_add,Finset.sum_sub_distrib,Finset.sum_add_distrib]
  have he (j : I) : PowerSeries.C (K i j)*(PowerSeries.X*(PowerSeries.C (h j)*inserted K hs h A R)) =
    PowerSeries.X*(PowerSeries.C (K i j)*PowerSeries.C (h j))*inserted K hs h A R := by ring
  have hf (j : I) : PowerSeries.C (K i j)*(PowerSeries.X^2*∑ l,PowerSeries.C (A j l)*inserted K hs h A (MvPolynomial.X l*R)) =
    PowerSeries.X^2*(PowerSeries.C (K i j)*∑ l,PowerSeries.C (A j l)*inserted K hs h A (MvPolynomial.X l*R)) := by ring
  simp only [he,hf,← Finset.mul_sum,← Finset.sum_mul]
  ring

end PolynomialInsertionWard
#print axioms PolynomialInsertionWard.system
