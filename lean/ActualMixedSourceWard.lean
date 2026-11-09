import FormalWickInsertion

noncomputable section
open scoped BigOperators
namespace ActualMixedSourceWard
open FormalDividedPowers FormalMixedExponential FormalWickInsertion MixedSourcePolynomials
variable {I S : Type*} [Fintype I] [Field S] [CharZero S]

def E (h : I → S) (A : I → I → S) : PowerSeries (MvPolynomial I S) :=
  mixed (S:=S) (LinearSourceExpansion.source h) (interaction A)

def Z (K : I → I → S) (hs : ∀ i j, K i j = K j i) (h : I → S) (A : I → I → S) :=
  moment K hs 1 (E h A)

def G (K : I → I → S) (hs : ∀ i j, K i j = K j i) (h : I → S) (A : I → I → S) (i : I) :=
  moment K hs (MvPolynomial.X i) (E h A)

def H (K : I → I → S) (hs : ∀ i j, K i j = K j i) (h : I → S) (A : I → I → S) (i j : I) :=
  moment K hs (MvPolynomial.X i * MvPolynomial.X j) (E h A)

theorem inserted_derivative (K : I → I → S) (hs : ∀ i j, K i j = K j i)
    (h : I → S) (A : I → I → S) (hA : ∀ i j, A i j = A j i)
    (R : MvPolynomial I S) (i : I) :
    moment K hs R (derivLift (MvPolynomial.pderiv i) (E h A)) =
      PowerSeries.X * (PowerSeries.C (h i) * moment K hs R (E h A)) -
      PowerSeries.X^2 * ∑ j, PowerSeries.C (A i j) * moment K hs (R * MvPolynomial.X j) (E h A) := by
  rw [E, mixed_derivative, source_derivative, interaction_derivative A hA i]
  change moment K hs R
    ((PowerSeries.C (MvPolynomial.C (h i)) * PowerSeries.X +
       PowerSeries.C (-(∑ j, A i j • MvPolynomial.X j)) * PowerSeries.X^2) * E h A) = _
  rw [add_mul, moment_add]
  simp only [mul_assoc, moment_C_mul]
  have hx (Q : MvPolynomial I S) : moment K hs Q (PowerSeries.X * E h A) =
      PowerSeries.X * moment K hs Q (E h A) := by
    simpa using moment_shift K hs Q (E h A) 1
  rw [hx, moment_shift]
  have hq : R * MvPolynomial.C (h i) = h i • R := by
    simp [Algebra.smul_def, mul_comm]
  rw [hq, moment_smul_insert]
  have ht : R * -(∑ j, A i j • MvPolynomial.X j) =
      -(∑ j, A i j • (R * MvPolynomial.X j)) := by
    simp [Finset.mul_sum, mul_smul_comm]
  rw [ht]
  have hn (Q : MvPolynomial I S) : moment K hs (-Q) (E h A) = -moment K hs Q (E h A) := by
    ext n; simp
  rw [hn, moment_sum_insert]
  simp only [moment_smul_insert]
  simp only [E]
  ring

theorem moment_zero (K : I → I → S) (hs : ∀ i j, K i j = K j i)
    (F : PowerSeries (MvPolynomial I S)) : moment K hs 0 F = 0 := by
  ext n; simp

theorem first_ward (K : I → I → S) (hs : ∀ i j, K i j = K j i)
    (h : I → S) (A : I → I → S) (hA : ∀ i j, A i j = A j i) (i : I) :
    G K hs h A i = ∑ k, PowerSeries.C (K i k) *
      (PowerSeries.X * (PowerSeries.C (h k) * Z K hs h A) -
       PowerSeries.X^2 * ∑ j, PowerSeries.C (A k j) * G K hs h A j) := by
  have hb := ibp K hs i 1 (E h A)
  simp only [mul_one, Derivation.map_one_eq_zero, moment_zero, zero_add] at hb
  change moment K hs (MvPolynomial.X i) (E h A) = _
  rw [hb]
  apply Finset.sum_congr rfl
  intro k _
  rw [inserted_derivative K hs h A hA]
  simp only [one_mul, G, Z]

theorem second_ward (K : I → I → S) (hs : ∀ i j, K i j = K j i)
    (h : I → S) (A : I → I → S) (hA : ∀ i j, A i j = A j i) (i j : I) :
    H K hs h A i j = PowerSeries.C (K i j) * Z K hs h A +
      ∑ k, PowerSeries.C (K i k) *
      (PowerSeries.X * (PowerSeries.C (h k) * G K hs h A j) -
       PowerSeries.X^2 * ∑ l, PowerSeries.C (A k l) * H K hs h A j l) := by
  classical
  have hb := ibp K hs i (MvPolynomial.X j) (E h A)
  change moment K hs (MvPolynomial.X i * MvPolynomial.X j) (E h A) = _
  rw [hb]
  simp only [mul_add, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_eq_single j]
    · simp [MvPolynomial.pderiv_X, Pi.single_apply, Z]
    · intro k _ hk
      simp [MvPolynomial.pderiv_X, Pi.single_apply, Ne.symm hk, moment_zero]
    · simp
  · apply Finset.sum_congr rfl
    intro k _
    rw [inserted_derivative K hs h A hA]
    rfl

end ActualMixedSourceWard
#print axioms ActualMixedSourceWard.inserted_derivative

#print axioms ActualMixedSourceWard.first_ward
#print axioms ActualMixedSourceWard.second_ward
