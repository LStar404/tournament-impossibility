import RankOneQuadraticODE

noncomputable section
namespace RankOneQuadraticUnitBranch
open RankOneQuadraticCoefficients RankOneQuadraticODE LinearSourcePairingFactor
variable {L S : Type*} [Fintype L] [Field S] [CharZero S]

theorem denominator_derivative (q : S) :
    PowerSeries.derivative (denominator q) = PowerSeries.C q := by
  simp [denominator, Derivation.leibniz]

theorem square_identity (C : L → L → S) (hs : ∀ i j, C i j = C j i)
    (h : L → S) (a : S) :
    (series C hs h a)^2 * denominator (a * quadratic C h) = 1 := by
  let F := series C hs h a
  let q := a * quadratic C h
  have ho : denominator q * PowerSeries.derivative F = PowerSeries.C (-q/2) * F :=
    ode C hs h a
  have hscale : (2 : PowerSeries S) * PowerSeries.C (-q/2) = -PowerSeries.C q := by
    rw [show (2 : PowerSeries S) = PowerSeries.C (2:S) by exact (map_natCast PowerSeries.C 2).symm, ← map_mul, ← map_neg]
    congr 1
    field_simp
    <;> ring
  apply PowerSeries.derivative.ext
  · rw [PowerSeries.derivative_one, Derivation.leibniz, PowerSeries.derivative_pow,
      denominator_derivative]
    simp only [smul_eq_mul]
    change F^2 * PowerSeries.C q + denominator q * (2 * F^(2-1) * PowerSeries.derivative F) = 0
    calc
      _ = 2 * F * (denominator q * PowerSeries.derivative F) + F^2 * PowerSeries.C q := by ring
      _ = (2 * PowerSeries.C (-q/2)) * F^2 + F^2 * PowerSeries.C q := by rw [ho]; ring
      _ = 0 := by rw [hscale]; ring
  · simp [F, q, denominator]

theorem series_isUnit (C : L → L → S) (hs : ∀ i j, C i j = C j i)
    (h : L → S) (a : S) : IsUnit (series C hs h a) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simp

/-- The constant term selects the unique unit branch, excluding its negative. -/
theorem unique_branch (C : L → L → S) (hs : ∀ i j, C i j = C j i)
    (h : L → S) (a : S) (G : PowerSeries S)
    (hG0 : G.constantCoeff = 1)
    (hG : G^2 * denominator (a * quadratic C h) = 1) :
    G = series C hs h a := by
  have hD : denominator (a * quadratic C h) ≠ 0 := by
    intro he
    have hc := congrArg PowerSeries.constantCoeff he
    simpa [denominator] using hc
  have hsq : G^2 = (series C hs h a)^2 :=
    mul_right_cancel₀ hD (hG.trans (square_identity C hs h a).symm)
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hsq with he | he
  · exact he
  · have hc := congrArg PowerSeries.constantCoeff he
    simp only [map_neg, constant_series, hG0] at hc
    have hh : (2:S) = 0 := by linear_combination hc
    exact (two_ne_zero hh).elim

end RankOneQuadraticUnitBranch
#print axioms RankOneQuadraticUnitBranch.square_identity
#print axioms RankOneQuadraticUnitBranch.series_isUnit

#print axioms RankOneQuadraticUnitBranch.unique_branch
