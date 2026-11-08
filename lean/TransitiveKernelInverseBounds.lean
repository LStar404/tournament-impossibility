import TransitiveKernelInverse
import MatrixEuclideanEntryBound
import Mathlib

noncomputable section
namespace TransitiveKernelInverseBounds
open TransitiveKernelInverse Matrix

lemma norm_one_add (a : ℂ) : ‖1+a‖ ≤ 1+‖a‖ := by
  simpa using norm_add_le (1 : ℂ) a

lemma norm_one_sub (a : ℂ) : ‖1-a‖ ≤ 1+‖a‖ := by
  simpa using norm_sub_le (1 : ℂ) a

lemma norm_H (n : ℕ) (a : ℂ) : ‖H n a‖ ≤ (1+‖a‖)^n := by
  rw [H, norm_div]
  norm_num only [Complex.norm_ofNat]
  calc
    _ ≤ (‖(1+a)^n‖+‖(1-a)^n‖)/2 := by
      exact div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
    _ ≤ ((1+‖a‖)^n+(1+‖a‖)^n)/2 := by
      simp only [norm_pow]
      gcongr
      · exact norm_one_add a
      · exact norm_one_sub a
    _ = _ := by ring

lemma numerator_diagonal (n : ℕ) (a : ℂ) (i : Fin n) :
    ‖numerator n a i i‖ ≤ (1+‖a‖)^(n-1) := by
  simpa [numerator] using norm_H (n-1) a

/-- Off-diagonal inverse numerators have an explicit factor |a|. This factor
is essential; dropping it would lose dimension-uniform operator control. -/
lemma numerator_offdiagonal (n : ℕ) (a : ℂ) (i j : Fin n) (hij : i ≠ j) :
    ‖numerator n a i j‖ ≤ ‖a‖*(1+‖a‖)^(n-2) := by
  rcases lt_or_gt_of_ne hij with h | h
  · have hp : (j.val-i.val-1)+(n-j.val+i.val-1)=n-2 := by
      have hi := i.isLt
      have hj := j.isLt
      simp only [Fin.lt_def] at h
      omega
    simp only [numerator, if_neg hij, if_pos h, norm_mul, norm_neg, norm_pow]
    calc
      _ ≤ ‖a‖*(1+‖a‖)^(j.val-i.val-1)*(1+‖a‖)^(n-j.val+i.val-1) := by
        gcongr
        · exact norm_one_sub a
        · exact norm_one_add a
      _ = ‖a‖*(1+‖a‖)^((j.val-i.val-1)+(n-j.val+i.val-1)) := by rw [pow_add]; ring
      _ = _ := by rw [hp]
  · have hp : (i.val-j.val-1)+(n-i.val+j.val-1)=n-2 := by
      have hi := i.isLt
      have hj := j.isLt
      simp only [Fin.lt_def] at h
      omega
    simp only [numerator, if_neg hij, if_neg (not_lt_of_ge h.le), norm_mul, norm_pow]
    calc
      _ ≤ ‖a‖*(1+‖a‖)^(i.val-j.val-1)*(1+‖a‖)^(n-i.val+j.val-1) := by
        gcongr
        · exact norm_one_add a
        · exact norm_one_sub a
      _ = ‖a‖*(1+‖a‖)^((i.val-j.val-1)+(n-i.val+j.val-1)) := by rw [pow_add]; ring
      _ = _ := by rw [hp]

lemma power_le_exp (n k : ℕ) (hn : 0 < n) (hk : k ≤ n) (a : ℂ) (R : ℝ)
    (ha : ‖a‖ ≤ R/(n : ℝ)) : (1+‖a‖)^k ≤ Real.exp R := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hscale : ‖a‖*(n : ℝ) ≤ R := (le_div_iff₀ hnR).mp ha
  have hkR : (k : ℝ) ≤ n := by exact_mod_cast hk
  have hmul : (k : ℝ)*‖a‖ ≤ R := by nlinarith [norm_nonneg a]
  calc
    _ ≤ (Real.exp ‖a‖)^k := by
      apply pow_le_pow_left₀ (by positivity)
      simpa [add_comm] using Real.add_one_le_exp ‖a‖
    _ = Real.exp ((k : ℝ)*‖a‖) := (Real.exp_nat_mul _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr hmul

lemma numerator_diagonal_exp (n : ℕ) (hn : 0 < n) (a : ℂ) (R : ℝ)
    (ha : ‖a‖ ≤ R/(n : ℝ)) (i : Fin n) :
    ‖numerator n a i i‖ ≤ Real.exp R :=
  (numerator_diagonal n a i).trans (power_le_exp n (n-1) hn (Nat.sub_le _ _) a R ha)

lemma numerator_offdiagonal_exp (n : ℕ) (hn : 0 < n) (a : ℂ) (R : ℝ)
    (ha : ‖a‖ ≤ R/(n : ℝ)) (i j : Fin n) (hij : i ≠ j) :
    ‖numerator n a i j‖ ≤ (R/(n : ℝ))*Real.exp R := by
  calc
    _ ≤ ‖a‖*(1+‖a‖)^(n-2) := numerator_offdiagonal n a i j hij
    _ ≤ ‖a‖*Real.exp R := mul_le_mul_of_nonneg_left
      (power_le_exp n (n-2) hn (Nat.sub_le _ _) a R ha) (norm_nonneg a)
    _ ≤ _ := mul_le_mul_of_nonneg_right ha (Real.exp_pos R).le

/-- Actual diagonal inverse estimate, conditional only on parameter size and
a lower bound for the explicit finite denominator. -/
theorem inverse_diagonal (m : ℕ) (a : ℂ) (R c : ℝ)
    (ha : ‖a‖ ≤ R/((m+1 : ℕ) : ℝ)) (hc : 0 < c) (hH : c ≤ ‖H (m+1) a‖)
    (i : Fin (m+1)) :
    ‖(TournamentHamiltonian.transitiveKernel (m+1) a)⁻¹ i i‖ ≤ Real.exp R/c := by
  have hpos : 0 < ‖H (m+1) a‖ := hc.trans_le hH
  have hnz : H (m+1) a ≠ 0 := norm_pos_iff.mp hpos
  rw [inverse_formula m a hnz]
  simp only [Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv]
  calc
    _ ≤ c⁻¹*Real.exp R := mul_le_mul
      (inv_anti₀ hc hH) (numerator_diagonal_exp (m+1) (by omega) a R ha i)
      (norm_nonneg _) (inv_nonneg.mpr hc.le)
    _ = _ := by ring

theorem inverse_offdiagonal (m : ℕ) (a : ℂ) (R c : ℝ)
    (ha : ‖a‖ ≤ R/((m+1 : ℕ) : ℝ)) (hc : 0 < c) (hH : c ≤ ‖H (m+1) a‖)
    (i j : Fin (m+1)) (hij : i ≠ j) :
    ‖(TournamentHamiltonian.transitiveKernel (m+1) a)⁻¹ i j‖ ≤
      (R/((m+1 : ℕ) : ℝ))*Real.exp R/c := by
  have hpos : 0 < ‖H (m+1) a‖ := hc.trans_le hH
  have hnz : H (m+1) a ≠ 0 := norm_pos_iff.mp hpos
  rw [inverse_formula m a hnz]
  simp only [Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv]
  calc
    _ ≤ c⁻¹*((R/((m+1 : ℕ) : ℝ))*Real.exp R) := mul_le_mul
      (inv_anti₀ hc hH) (numerator_offdiagonal_exp (m+1) (by omega) a R ha i j hij)
      (norm_nonneg _) (inv_nonneg.mpr hc.le)
    _ = _ := by ring

/-- Dimension-uniform Euclidean operator bound. The diagonal is separated
before applying the Frobenius estimate to the O(1/n) off-diagonal remainder. -/
theorem inverse_operator (m : ℕ) (a : ℂ) (R c : ℝ)
    (ha : ‖a‖ ≤ R/((m+1 : ℕ) : ℝ)) (hc : 0 < c) (hH : c ≤ ‖H (m+1) a‖) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin (m+1))
      ((TournamentHamiltonian.transitiveKernel (m+1) a)⁻¹)‖ ≤
      (1+R)*Real.exp R/c := by
  have hnR : (0 : ℝ) < ((m+1 : ℕ) : ℝ) := by positivity
  have hR : 0 ≤ R := by
    have hh := (le_div_iff₀ hnR).mp ha
    nlinarith [norm_nonneg a]
  have hnz : H (m+1) a ≠ 0 := norm_pos_iff.mp (hc.trans_le hH)
  let A := (TournamentHamiltonian.transitiveKernel (m+1) a)⁻¹
  let d : ℂ := (H (m+1) a)⁻¹ * H m a
  let E : Matrix (Fin (m+1)) (Fin (m+1)) ℂ := A-d • 1
  have hdiag (i : Fin (m+1)) : A i i=d := by
    simp [A, d, inverse_formula m a hnz, numerator]
  have hd : ‖d‖ ≤ Real.exp R/c := by
    rw [← hdiag 0]
    exact inverse_diagonal m a R c ha hc hH 0
  have hC : 0 ≤ R*Real.exp R/c := by positivity
  have he (i j : Fin (m+1)) : ‖E i j‖ ≤ (R*Real.exp R/c)/((m+1 : ℕ) : ℝ) := by
    by_cases hij : i=j
    · subst j
      simp [E, hdiag]
      positivity
    · have hh := inverse_offdiagonal m a R c ha hc hH i j hij
      simp only [E, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
        if_neg hij, mul_zero, sub_zero]
      change ‖(TournamentHamiltonian.transitiveKernel (m+1) a)⁻¹ i j‖ ≤ _
      convert hh using 1 <;> ring
  have h := MatrixEuclideanEntryBound.scalar_identity_add_error
    (n := m+1) (by omega) d E hd hC he
  have hid : d • (1 : Matrix (Fin (m+1)) (Fin (m+1)) ℂ)+E=A := by dsimp [E]; abel
  rw [hid] at h
  change ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin (m+1)) A‖ ≤ _
  convert h using 1 <;> ring

end TransitiveKernelInverseBounds
#print axioms TransitiveKernelInverseBounds.inverse_diagonal
#print axioms TransitiveKernelInverseBounds.inverse_offdiagonal

#print axioms TransitiveKernelInverseBounds.inverse_operator
