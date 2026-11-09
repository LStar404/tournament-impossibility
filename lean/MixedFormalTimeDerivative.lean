import ActualMixedSourceWard
import Mathlib.RingTheory.PowerSeries.Derivative

noncomputable section
namespace MixedFormalTimeDerivative
open FormalDividedPowers FormalMixedExponential
variable {S P : Type*} [Field S] [CharZero S] [CommRing P] [Algebra S P]

theorem divided_step (R : P) (n : ℕ) :
    (n+1) • divided (S:=S) R (n+1) = R * divided (S:=S) R n := by
  unfold divided
  rw [← Nat.cast_smul_eq_nsmul S, smul_smul]
  have hn : (n:S)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have he : (n+1:ℕ)*(1/((n+1).factorial:S)) = 1/(n.factorial:S) := by
    rw [Nat.factorial_succ]; push_cast; field_simp
  rw [he, pow_succ]
  simp [Algebra.smul_def, mul_assoc, mul_comm, mul_left_comm]

theorem exponential_time_derivative (R : P) :
    PowerSeries.derivative (exponential (S:=S) R) = PowerSeries.C R * exponential (S:=S) R := by
  ext n
  simp only [PowerSeries.coeff_derivative, coeff_exponential, PowerSeries.coeff_C_mul]
  simpa [nsmul_eq_mul, mul_comm] using divided_step (S:=S) R n

theorem quadratic_time_derivative (R : P) :
    PowerSeries.derivative (PowerSeries.expand 2 (by decide) (exponential (S:=S) R)) =
      2 * PowerSeries.X * (PowerSeries.C R * PowerSeries.expand 2 (by decide) (exponential (S:=S) R)) := by
  rw [show (2 : PowerSeries P) * PowerSeries.X * _ =
    PowerSeries.C (2:P) * (PowerSeries.X * (PowerSeries.C R * PowerSeries.expand 2 (by decide) (exponential (S:=S) R))) by
      rw [show PowerSeries.C (2:P) = 2 from map_natCast PowerSeries.C 2]; ring]
  ext n
  cases n with
  | zero => simp [PowerSeries.coeff_derivative, PowerSeries.coeff_expand]
  | succ n =>
    simp only [PowerSeries.coeff_derivative, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul]
    rcases Nat.even_or_odd n with ⟨k,hk⟩ | ⟨k,hk⟩
    · have hn : n=2*k := by omega
      rw [hn, show 2*k+1+1=2*(k+1) by omega]
      simp only [PowerSeries.coeff_expand_mul, coeff_exponential]
      have hh := divided_step (S:=S) R k
      simp only [nsmul_eq_mul] at hh
      push_cast at hh ⊢
      linear_combination 2 * hh
    · have hn : n=2*k+1 := by omega
      rw [hn]
      have h1 : ¬ 2 ∣ 2*k+1 := by omega
      have h2 : ¬ 2 ∣ 2*k+1+1+1 := by omega
      simp [PowerSeries.coeff_expand, h1, h2]

theorem mixed_time_derivative (L H : P) :
    PowerSeries.derivative (mixed (S:=S) L H) =
      (PowerSeries.C L + 2 * PowerSeries.X * PowerSeries.C H) * mixed (S:=S) L H := by
  unfold mixed
  rw [Derivation.leibniz, exponential_time_derivative, quadratic_time_derivative]
  simp only [smul_eq_mul]
  ring

theorem lift_time_derivative (f : P →ₗ[S] S) (F : PowerSeries P) :
    PowerSeries.derivative (FormalLinearLift.lift f F) =
      FormalLinearLift.lift f (PowerSeries.derivative F) := by
  ext n
  simp only [PowerSeries.coeff_derivative, FormalLinearLift.coeff_lift]
  simpa only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one, mul_comm] using
    (map_nsmul f (n+1) (F.coeff (n+1))).symm

end MixedFormalTimeDerivative
#print axioms MixedFormalTimeDerivative.quadratic_time_derivative
