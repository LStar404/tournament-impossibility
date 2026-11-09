import FactorizedResidualIdentity
import PolynomialTiltedRecurrence

noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace ResidualInsertionConvolution
open FormalWickInsertion FormalLinearLift ActualMixedSourceWard PolynomialTiltedRecurrence
variable {I S : Type*} [Fintype I] [Field S] [CharZero S]

def normalizedCore (K : I → I → S) (hs : ∀ i j,K i j=K j i)
    (h : I → S) (A : I → I → S) : PowerSeries (MvPolynomial I S) :=
  PowerSeries.map (algebraMap S (MvPolynomial I S)) (Z K hs h A)⁻¹ * E h A

theorem moment_normalizedCore (K : I → I → S) (hs : ∀ i j,K i j=K j i)
    (h : I → S) (A : I → I → S) (R : MvPolynomial I S) :
    moment K hs R (normalizedCore K hs h A)=tilted K hs h A R := by
  unfold normalizedCore moment
  rw [lift_scalar_series]
  exact mul_comm _ _

/-- Explicit finite coefficient insertion sum, not multiplication of Wick values. -/
def insertionConvolution (K : I → I → S) (hs : ∀ i j,K i j=K j i)
    (h : I → S) (A : I → I → S) (R : PowerSeries (MvPolynomial I S)) : PowerSeries S :=
  PowerSeries.mk (fun n => ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal n,
    (tilted K hs h A (R.coeff ab.1)).coeff ab.2)

theorem convolution_eq_lift (K : I → I → S) (hs : ∀ i j,K i j=K j i)
    (h : I → S) (A : I → I → S) (R : PowerSeries (MvPolynomial I S)) :
    insertionConvolution K hs h A R =
      lift (OccurrenceWickPolynomial.wick K hs) (R*normalizedCore K hs h A) := by
  ext n
  simp only [insertionConvolution,PowerSeries.coeff_mk,coeff_lift,PowerSeries.coeff_mul,map_sum]
  apply Finset.sum_congr rfl
  intro ab hab
  rw [← moment_normalizedCore K hs h A (R.coeff ab.1),coeff_moment]

theorem normalized_identity (K : I → I → S) (hs : ∀ i j,K i j=K j i)
    (h : I → S) (A : I → I → S) (R : PowerSeries (MvPolynomial I S)) :
    Z K hs h A * insertionConvolution K hs h A R =
      lift (OccurrenceWickPolynomial.wick K hs) (E h A*R) := by
  rw [convolution_eq_lift]
  have he : R*normalizedCore K hs h A =
      PowerSeries.map (algebraMap S (MvPolynomial I S)) (Z K hs h A)⁻¹ * (E h A*R) := by
    unfold normalizedCore; ring
  rw [he,lift_scalar_series,← mul_assoc]
  have hz : Z K hs h A*(Z K hs h A)⁻¹=1 :=
    PowerSeries.mul_inv_cancel _ (by rw [ActualMixedSourceTimeODE.Z_initial]; exact one_ne_zero)
  rw [hz,one_mul]

/-- Actual finite shifted product = true Wick core times normalized residual insertion. -/
theorem actual_shifted_identity (K : I → I → S) (hs : ∀ i j,K i j=K j i) :
    lift (OccurrenceWickPolynomial.wick K hs) (FactorizedResidualIdentity.shiftedProduct (I:=I) (S:=S)) =
      Z K hs (fun _ => 1) (1 : Matrix I I S) *
        insertionConvolution K hs (fun _ => 1) (1 : Matrix I I S)
          (FactorizedResidualIdentity.actualResidual (I:=I) (S:=S)) := by
  erw [normalized_identity K hs (fun _ => 1) (1 : Matrix I I S),FactorizedResidualIdentity.actual_factorization]

end ResidualInsertionConvolution
#print axioms ResidualInsertionConvolution.actual_shifted_identity
#print axioms ResidualInsertionConvolution.normalized_identity
