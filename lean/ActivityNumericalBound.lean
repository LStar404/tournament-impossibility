import ActivityFactorialSuppression
noncomputable section
namespace ActivityNumericalBound

theorem factorial_core (j b D e s : ℕ) (hj : 1 ≤ j) (hb : b ≤ 2*j)
    (hD : D ≤ 6*j) (he : e ≤ 3*j) (hes : e+s=j+b)
    (M : ℝ) (hM : 1 ≤ M) :
    (2:ℝ)^b*2^D*(D:ℝ)^e*M^(e+s)/(b.factorial:ℝ) ≤
      ((2:ℝ)^8*6^3*Real.exp 1*M^3)^j*(j:ℝ)^j := by
  have h2 : (2:ℝ)^(b+D) ≤ 2^(8*j) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h6 : (6:ℝ)^e ≤ 6^(3*j) := pow_le_pow_right₀ (by norm_num) he
  have hMp : M^(e+s) ≤ M^(3*j) := pow_le_pow_right₀ hM (by omega)
  have hDj : (D:ℝ)^e ≤ ((6:ℝ)*(j:ℝ))^e := by
    apply pow_le_pow_left₀ (Nat.cast_nonneg D)
    exact_mod_cast hD
  have hpos : 0 ≤ M := by linarith
  calc
    _ ≤ (2:ℝ)^b*2^D*((6:ℝ)*(j:ℝ))^e*M^(e+s)/(b.factorial:ℝ) := by gcongr
    _ = (2:ℝ)^(b+D)*6^e*M^(e+s)*((j:ℝ)^e/(b.factorial:ℝ)) := by rw [pow_add,mul_pow]; ring
    _ ≤ (2:ℝ)^(8*j)*6^(3*j)*M^(3*j)*((j:ℝ)^e/(b.factorial:ℝ)) := by gcongr
    _ ≤ (2:ℝ)^(8*j)*6^(3*j)*M^(3*j)*((j:ℝ)^j*Real.exp (j:ℝ)) := by
      apply mul_le_mul_of_nonneg_left (ActivityFactorialSuppression.suppression j b e hj (by omega))
      positivity
    _ = _ := by
      rw [show Real.exp (j:ℝ)=(Real.exp 1)^j by rw [← Real.exp_nat_mul]; simp]
      simp only [pow_mul,mul_pow]
      ring

theorem scaled (n j b D e s : ℕ) (hn : 0<n) (hj : 1 ≤ j) (hb : b ≤ 2*j)
    (hD : D ≤ 6*j) (he : e ≤ 3*j) (hes : e+s=j+b)
    (M : ℝ) (hM : 1 ≤ M) :
    (1/(b.factorial:ℝ))*(2*(n:ℝ))^b*((2:ℝ)^D*(D:ℝ)^e*(M/n)^e*(M/n)^s) ≤
      (((2:ℝ)^8*6^3*Real.exp 1*M^3)*(j:ℝ)/(n:ℝ))^j := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hid : (1/(b.factorial:ℝ))*(2*(n:ℝ))^b*((2:ℝ)^D*(D:ℝ)^e*(M/n)^e*(M/n)^s)=
      ((2:ℝ)^b*2^D*(D:ℝ)^e*M^(e+s)/(b.factorial:ℝ))/(n:ℝ)^j := by
    calc
      _ = ((2:ℝ)^D*(D:ℝ)^e*M^(e+s)/(b.factorial:ℝ))*
          (((2:ℝ)*(n:ℝ))^b/(n:ℝ)^(e+s)) := by
        simp only [pow_add,div_pow,mul_pow]
        field_simp
      _ = ((2:ℝ)^D*(D:ℝ)^e*M^(e+s)/(b.factorial:ℝ))*((2:ℝ)^b/(n:ℝ)^j) := by
        rw [ActivityFactorialSuppression.dimension_cancel n b e s j hn hes]
      _ = _ := by ring
  rw [hid,div_pow,mul_pow]
  exact div_le_div_of_nonneg_right (factorial_core j b D e s hj hb hD he hes M hM) (by positivity)
end ActivityNumericalBound
#print axioms ActivityNumericalBound.scaled
