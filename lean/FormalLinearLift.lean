import FullWickPolynomialIBP
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Expand

noncomputable section
open scoped BigOperators
namespace FormalLinearLift
variable {S P : Type*} [CommRing S] [CommRing P] [Algebra S P]

/-- Coefficientwise lift of a linear map; deliberately not a ring homomorphism. -/
def lift (f : P →ₗ[S] S) (F : PowerSeries P) : PowerSeries S :=
  PowerSeries.mk (fun n => f (F.coeff n))

@[simp] theorem coeff_lift (f : P →ₗ[S] S) (F : PowerSeries P) (n : ℕ) :
    (lift f F).coeff n = f (F.coeff n) := by simp [lift]

theorem lift_add (f : P →ₗ[S] S) (F G : PowerSeries P) :
    lift f (F+G)=lift f F+lift f G := by ext n; simp

theorem lift_scalar_series (f : P →ₗ[S] S) (A : PowerSeries S) (F : PowerSeries P) :
    lift f (PowerSeries.map (algebraMap S P) A * F) = A * lift f F := by
  ext n
  simp only [coeff_lift, PowerSeries.coeff_mul, map_sum, PowerSeries.coeff_map]
  apply Finset.sum_congr rfl
  rintro ⟨i,j⟩ _
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

def insert {I : Type*} [Fintype I] (K : I → I → S)
    (hs : ∀ i j, K i j = K j i) (R : MvPolynomial I S) :
    MvPolynomial I S →ₗ[S] S :=
  (OccurrenceWickPolynomial.wick K hs).comp (LinearMap.mulLeft S R)

@[simp] theorem insert_apply {I : Type*} [Fintype I] (K : I → I → S)
    (hs : ∀ i j, K i j = K j i) (R Q : MvPolynomial I S) :
    insert K hs R Q = OccurrenceWickPolynomial.wick K hs (R*Q) := rfl

end FormalLinearLift
#print axioms FormalLinearLift.lift_scalar_series
