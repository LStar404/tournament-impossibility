import MixedSourcePolynomials

noncomputable section
open scoped BigOperators
namespace FormalWickInsertion
open FormalLinearLift OccurrenceWickPolynomial FormalDividedPowers
variable {I S : Type*} [Fintype I] [Field S] [CharZero S]

def moment (K : I → I → S) (hs : ∀ i j, K i j = K j i)
    (R : MvPolynomial I S) (F : PowerSeries (MvPolynomial I S)) : PowerSeries S :=
  lift (insert K hs R) F

@[simp] theorem coeff_moment (K : I → I → S) (hs : ∀ i j, K i j = K j i)
    (R : MvPolynomial I S) (F : PowerSeries (MvPolynomial I S)) (n : ℕ) :
    (moment K hs R F).coeff n = wick K hs (R * F.coeff n) := by simp [moment]

theorem moment_add (K : I → I → S) (hs : ∀ i j, K i j = K j i)
    (R : MvPolynomial I S) (F G : PowerSeries (MvPolynomial I S)) :
    moment K hs R (F+G) = moment K hs R F + moment K hs R G := by
  ext n; simp [mul_add]

theorem moment_neg (K : I → I → S) (hs : ∀ i j, K i j = K j i)
    (R : MvPolynomial I S) (F : PowerSeries (MvPolynomial I S)) :
    moment K hs R (-F) = -moment K hs R F := by ext n; simp

theorem moment_C_mul (K : I → I → S) (hs : ∀ i j, K i j = K j i)
    (R Q : MvPolynomial I S) (F : PowerSeries (MvPolynomial I S)) :
    moment K hs R (PowerSeries.C Q * F) = moment K hs (R*Q) F := by
  ext n; simp [mul_assoc]

theorem moment_shift (K : I → I → S) (hs : ∀ i j, K i j = K j i)
    (R : MvPolynomial I S) (F : PowerSeries (MvPolynomial I S)) (k : ℕ) :
    moment K hs R (PowerSeries.X^k * F) = PowerSeries.X^k * moment K hs R F := by
  ext n
  simp only [coeff_moment, PowerSeries.coeff_X_pow_mul']
  split_ifs <;> simp

theorem moment_smul_insert (K : I → I → S) (hs : ∀ i j, K i j = K j i)
    (R : MvPolynomial I S) (F : PowerSeries (MvPolynomial I S)) (a : S) :
    moment K hs (a • R) F = PowerSeries.C a * moment K hs R F := by
  ext n
  simp [smul_mul_assoc]

theorem moment_sum_insert (K : I → I → S) (hs : ∀ i j, K i j = K j i)
    (R : I → MvPolynomial I S) (F : PowerSeries (MvPolynomial I S)) :
    moment K hs (∑ i, R i) F = ∑ i, moment K hs (R i) F := by
  ext n; simp [Finset.sum_mul]

theorem ibp (K : I → I → S) (hs : ∀ i j, K i j = K j i)
    (i : I) (R : MvPolynomial I S) (F : PowerSeries (MvPolynomial I S)) :
    moment K hs (MvPolynomial.X i * R) F =
      ∑ j, PowerSeries.C (K i j) *
        (moment K hs (MvPolynomial.pderiv j R) F +
          moment K hs R (derivLift (MvPolynomial.pderiv j) F)) := by
  ext n
  simp only [coeff_moment, map_sum, map_add, PowerSeries.coeff_C_mul, coeff_derivLift]
  rw [mul_assoc, FullWickPolynomialIBP.wick_X_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [MvPolynomial.pderiv_mul, map_add]

end FormalWickInsertion
#print axioms FormalWickInsertion.ibp
