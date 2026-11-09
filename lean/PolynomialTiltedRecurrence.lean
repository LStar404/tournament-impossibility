import PolynomialInsertionWard
import ActualMixedSourceTimeODE

noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace PolynomialTiltedRecurrence
open Matrix PolynomialInsertionWard ActualMixedSourceWard ActualMixedWardMatrix MixedWardSolution MixedWardUnit
variable {I S : Type*} [Fintype I] [Field S] [CharZero S]

theorem inserted_recurrence (K : I → I → S) (hs : ∀ i j, K i j=K j i)
    (h : I → S) (A : I → I → S) (hA : ∀ i j, A i j=A j i)
    (R : MvPolynomial I S) (i : I) :
    inserted K hs h A (MvPolynomial.X i*R) =
      ∑ j,covariance K A i j*inserted K hs h A (MvPolynomial.pderiv j R) +
        PowerSeries.X*response K A h i*inserted K hs h A R := by
  have hh := funext (system K hs h A hA R)
  have hx := congrArg (fun f => (block K A)⁻¹.mulVec f) hh
  rw [Matrix.mulVec_mulVec,left_inverse,Matrix.one_mulVec] at hx
  rw [congrFun hx i]
  simp only [response,covariance,Matrix.mulVec,Matrix.mul_apply,Matrix.of_apply,dotProduct,
    mul_add,Finset.sum_add_distrib,Finset.mul_sum,Finset.sum_mul]
  congr 1
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    ring
  · apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    ring

def tilted (K : I → I → S) (hs : ∀ i j, K i j=K j i)
    (h : I → S) (A : I → I → S) (R : MvPolynomial I S) : PowerSeries S :=
  inserted K hs h A R * (Z K hs h A)⁻¹

theorem core_unit (K : I → I → S) (hs : ∀ i j, K i j=K j i)
    (h : I → S) (A : I → I → S) : IsUnit (Z K hs h A) := by
  rw [PowerSeries.isUnit_iff_constantCoeff,ActualMixedSourceTimeODE.Z_initial]
  exact isUnit_one

theorem tilted_one (K : I → I → S) (hs : ∀ i j, K i j=K j i)
    (h : I → S) (A : I → I → S) : tilted K hs h A 1=1 := by
  change Z K hs h A*(Z K hs h A)⁻¹=1
  exact PowerSeries.mul_inv_cancel _ (by rw [ActualMixedSourceTimeODE.Z_initial]; exact one_ne_zero)

/-- True arbitrary-polynomial tilted recurrence. The unscaled variable has
mean u*response and covariance V; physical uX scales these by u again. -/
theorem tilted_recurrence (K : I → I → S) (hs : ∀ i j, K i j=K j i)
    (h : I → S) (A : I → I → S) (hA : ∀ i j, A i j=A j i)
    (R : MvPolynomial I S) (i : I) :
    tilted K hs h A (MvPolynomial.X i*R) =
      ∑ j,covariance K A i j*tilted K hs h A (MvPolynomial.pderiv j R) +
        PowerSeries.X*response K A h i*tilted K hs h A R := by
  unfold tilted
  rw [inserted_recurrence K hs h A hA]
  simp only [add_mul,Finset.sum_mul,mul_assoc]

end PolynomialTiltedRecurrence
#print axioms PolynomialTiltedRecurrence.tilted_recurrence
#print axioms PolynomialTiltedRecurrence.tilted_one
