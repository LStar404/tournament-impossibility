import RankOneQuadraticCoefficients

noncomputable section
namespace RankOneQuadraticODE
open RankOneQuadraticCoefficients LinearSourcePairingFactor
variable {L S : Type*} [Fintype L] [Field S] [CharZero S]

def denominator (q : S) : PowerSeries S := 1 + PowerSeries.C q * PowerSeries.X

theorem ode (C : L → L → S) (hs : ∀ i j, C i j = C j i)
    (h : L → S) (a : S) :
    denominator (a * quadratic C h) * PowerSeries.derivative (series C hs h a) =
      PowerSeries.C (-(a * quadratic C h)/2) * series C hs h a := by
  unfold denominator
  rw [add_mul, one_mul, mul_assoc]
  ext k
  simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_derivative,
    coeff_series]
  cases k with
  | zero =>
    have hh := coefficient_step C hs h a 0
    simpa using hh
  | succ k =>
    have hx : (PowerSeries.X * PowerSeries.derivative (series C hs h a)).coeff (k+1) =
        coefficient C hs h a (k+1) * (k+1:S) := by
      simp [PowerSeries.coeff_derivative]
    rw [hx]
    have hh := coefficient_step C hs h a (k+1)
    push_cast at hh ⊢
    linear_combination hh

end RankOneQuadraticODE
#print axioms RankOneQuadraticODE.ode
