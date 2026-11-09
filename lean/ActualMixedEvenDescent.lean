import MixedEvenCandidate

noncomputable section
namespace ActualMixedEvenDescent
open ActualMixedSourceWard
variable {I S : Type*} [Fintype I] [Field S] [CharZero S] [Algebra ℚ S]

/-- Actual even Wick coefficients; not defined by a determinant formula. -/
def series (K : I → I → S) (hK : ∀ i j, K i j=K j i) (h : I → S) (A : I → I → S) : PowerSeries S :=
  PowerSeries.mk (fun n => (Z K hK h A).coeff (2*n))

theorem actual_expansion (K : I → I → S) (hK : ∀ i j, K i j=K j i)
    (A : I → I → S) (hA : ∀ i j, A i j=A j i) (h : I → S) :
    Z K hK h A = PowerSeries.expand 2 (by decide) (MixedEvenCandidate.candidate K A h) := by
  rw [MixedEvenCandidate.expand_candidate]
  exact ActualMixedDeterminantFormula.actual_formula K hK A hA h

theorem formula (K : I → I → S) (hK : ∀ i j, K i j=K j i)
    (A : I → I → S) (hA : ∀ i j, A i j=A j i) (h : I → S) :
    series K hK h A = MixedEvenCandidate.candidate K A h := by
  ext n
  simp only [series, PowerSeries.coeff_mk, actual_expansion K hK A hA h,
    PowerSeries.coeff_expand_mul]

theorem odd_coeff (K : I → I → S) (hK : ∀ i j, K i j=K j i)
    (A : I → I → S) (hA : ∀ i j, A i j=A j i) (h : I → S) (n : ℕ) :
    (Z K hK h A).coeff (2*n+1)=0 := by
  rw [actual_expansion K hK A hA h]
  apply PowerSeries.coeff_expand_of_not_dvd
  omega

theorem expand_series (K : I → I → S) (hK : ∀ i j, K i j=K j i)
    (A : I → I → S) (hA : ∀ i j, A i j=A j i) (h : I → S) :
    PowerSeries.expand 2 (by decide) (series K hK h A)= Z K hK h A := by
  rw [formula K hK A hA h, ← actual_expansion K hK A hA h]

end ActualMixedEvenDescent
#print axioms ActualMixedEvenDescent.formula
#print axioms ActualMixedEvenDescent.odd_coeff
