import ActualMixedSourceTimeODE

noncomputable section
namespace FormalFirstOrderUniqueness
variable {S : Type*} [Field S] [CharZero S]

theorem unique (a f g : PowerSeries S)
    (hf : PowerSeries.derivative f = a*f) (hg : PowerSeries.derivative g = a*g)
    (h0 : f.constantCoeff = g.constantCoeff) : f = g := by
  ext m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    cases m with
    | zero => simpa using h0
    | succ n =>
      have hp : (a*f).coeff n = (a*g).coeff n := by
        simp only [PowerSeries.coeff_mul]
        apply Finset.sum_congr rfl
        intro ij hij
        have hj : ij.2 < n+1 := by
          have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
          omega
        rw [ih ij.2 hj]
      rw [← hf, ← hg, PowerSeries.coeff_derivative, PowerSeries.coeff_derivative] at hp
      exact mul_right_cancel₀ (by exact_mod_cast Nat.succ_ne_zero n) hp

end FormalFirstOrderUniqueness
#print axioms FormalFirstOrderUniqueness.unique
