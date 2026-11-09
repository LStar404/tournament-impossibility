import FormalLinearLift

noncomputable section
namespace FormalDividedPowers
variable {S P : Type*} [Field S] [CharZero S] [CommRing P] [Algebra S P]

def divided (R : P) (n : ℕ) : P := (1/(n.factorial:S)) • R^n

def exponential (R : P) : PowerSeries P := PowerSeries.mk (divided (S:=S) R)

@[simp] theorem coeff_exponential (R : P) (n : ℕ) :
    (exponential (S:=S) R).coeff n = divided (S:=S) R n := by simp [exponential]

@[simp] theorem divided_zero (R : P) : divided (S:=S) R 0 = 1 := by simp [divided]

def derivLift (D : Derivation S P P) (F : PowerSeries P) : PowerSeries P :=
  PowerSeries.mk (fun n => D (F.coeff n))

@[simp] theorem coeff_derivLift (D : Derivation S P P) (F : PowerSeries P) (n : ℕ) :
    (derivLift D F).coeff n = D (F.coeff n) := by simp [derivLift]

theorem divided_derivative (D : Derivation S P P) (R : P) (n : ℕ) :
    D (divided (S:=S) R (n+1)) = D R * divided (S:=S) R n := by
  unfold divided
  change D.toLinearMap ((1/((n+1).factorial:S)) • R^(n+1)) = _
  rw [D.toLinearMap.map_smul]
  change (1/((n+1).factorial:S)) • D (R^(n+1)) = _
  rw [Derivation.leibniz_pow]
  simp only [Nat.add_sub_cancel]
  rw [← Nat.cast_smul_eq_nsmul S, smul_smul]
  have hn : (n:S)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have he : (1/((n+1).factorial:S)) * (n+1:ℕ) = 1/(n.factorial:S) := by
    rw [Nat.factorial_succ]
    push_cast
    field_simp
  rw [he]
  simp [Algebra.smul_def, mul_comm, mul_left_comm, mul_assoc]

theorem derivLift_mul (D : Derivation S P P) (F G : PowerSeries P) :
    derivLift D (F*G) = derivLift D F*G + F*derivLift D G := by
  ext n
  simp only [coeff_derivLift, PowerSeries.coeff_mul, map_sum, map_add,
    Derivation.leibniz, smul_eq_mul, Finset.sum_add_distrib]
  simp only [add_comm, mul_comm]

theorem exponential_derivative (D : Derivation S P P) (R : P) :
    derivLift D (exponential (S:=S) R) =
      PowerSeries.C (D R) * (PowerSeries.X * exponential (S:=S) R) := by
  ext n
  cases n with
  | zero => simp
  | succ n => simp [divided_derivative]

end FormalDividedPowers
#print axioms FormalDividedPowers.divided_derivative
#print axioms FormalDividedPowers.exponential_derivative
