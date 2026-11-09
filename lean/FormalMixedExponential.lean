import FormalDividedPowers

noncomputable section
namespace FormalMixedExponential
open FormalDividedPowers
variable {S P : Type*} [Field S] [CharZero S] [CommRing P] [Algebra S P]

def mixed (L H : P) : PowerSeries P :=
  exponential (S:=S) L * PowerSeries.expand 2 (by decide) (exponential (S:=S) H)

theorem derivLift_expand (D : Derivation S P P) (F : PowerSeries P) :
    derivLift D (PowerSeries.expand 2 (by decide) F) =
      PowerSeries.expand 2 (by decide) (derivLift D F) := by
  ext n
  simp only [coeff_derivLift, PowerSeries.coeff_expand]
  split_ifs <;> simp

theorem mixed_derivative (D : Derivation S P P) (L H : P) :
    derivLift D (mixed (S:=S) L H) =
      (PowerSeries.C (D L) * PowerSeries.X + PowerSeries.C (D H) * PowerSeries.X^2) *
        mixed (S:=S) L H := by
  unfold mixed
  rw [derivLift_mul, exponential_derivative, derivLift_expand, exponential_derivative]
  simp only [map_mul, PowerSeries.expand_C, PowerSeries.expand_X]
  ring

theorem coeff_mixed (L H : P) (n : ℕ) :
    (mixed (S:=S) L H).coeff n =
      ∑ jk ∈ Finset.HasAntidiagonal.antidiagonal n, divided (S:=S) L jk.1 *
        (if 2 ∣ jk.2 then divided (S:=S) H (jk.2/2) else 0) := by
  simp [mixed, PowerSeries.coeff_mul, PowerSeries.coeff_expand]

end FormalMixedExponential
#print axioms FormalMixedExponential.mixed_derivative
#print axioms FormalMixedExponential.coeff_mixed
