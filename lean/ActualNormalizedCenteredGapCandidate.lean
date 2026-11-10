import IndependentCenteredRestrictionCandidate
import ActualPrescalingNormalization
import TournamentSkewMargin

/-! Actual normalized tournament center bound, isolated verification batch.
No target spectral bound is assumed. No extremality conclusion. -/
set_option autoImplicit false
noncomputable section
namespace ActualNormalizedCenteredGapCandidate
open Matrix Finset
open scoped Matrix.Norms.L2Operator
open TournamentHamiltonian ActualTournamentPrescalingBounds
open ActualPrescalingNormalization TournamentPrescalingMass TournamentPrescalingMassBound
open PermanentSpectralFrame IndependentCenteredRestrictionCandidate
variable {n : ℕ}

def castMatrix (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  ComplexifiedSkewBound.complexify A

def errorBudget (T : Tournament n) (a0 : ℝ) : ℝ :=
  128*(scaleCap a0)^4*tau (normalizedScore T)/(n:ℝ)+
    512*(scaleCap a0)^4*(massBound T a0)^2/(n:ℝ)^2

lemma compress_norm (hn : 0 < n) (M : Matrix (Fin n) (Fin n) ℂ) :
    ‖proj n*M*proj n‖ ≤ ‖M‖ := by
  have hp := proj_norm hn
  calc
    _ ≤ (‖proj n‖*‖M‖)*‖proj n‖ :=
      (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ (1*‖M‖)*1 := by gcongr
    _ = _ := by ring

lemma base_split (T : Tournament n) (hn : 2 ≤ n) :
    castMatrix (baseMatrix T) =
      ((n:ℂ)/((n:ℂ)-1)) • averaging n +
      ((n:ℂ)-1)⁻¹ • (castMatrix (signMatrix T)-1) := by
  have hn0 : (n:ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hn1 : (n:ℂ)-1 ≠ 0 := by
    have : (n:ℝ)-1 > 0 := by
      have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
      linarith
    exact_mod_cast (ne_of_gt this)
  ext i j
  simp only [castMatrix, ComplexifiedSkewBound.complexify, baseMatrix,
    Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply,
    smul_eq_mul, averaging, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_sub,
    Complex.ofReal_one, Complex.ofReal_natCast, apply_ite]
  split_ifs <;> norm_num only [Complex.ofReal_one, Complex.ofReal_zero] <;> field_simp <;> ring

lemma base_center_bound (T : Tournament n) (hn : 24 ≤ n) :
    ‖proj n*castMatrix (baseMatrix T)*proj n‖ ≤ 19/23 := by
  have hn2 : 2 ≤ n := by omega
  have hn0 : 0 < n := by omega
  have hnR : (24:ℝ) ≤ n := by exact_mod_cast hn
  have hden : 0 < (n:ℝ)-1 := by linarith
  have hs : ‖castMatrix (signMatrix T)‖ ≤ (n:ℝ)*(17/24) := by
    rw [← Matrix.l2_opNorm_toEuclideanCLM]
    apply TournamentSkewMargin.unnormalized _ (fun i j => signMatrix_skew T j i)
    intro i j
    simp only [signMatrix]
    split_ifs <;> norm_num
  have hid : ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 1 := by
    rw [← Matrix.l2_opNorm_toEuclideanCLM, map_one]
    exact ContinuousLinearMap.norm_id_le
  have hz : proj n*averaging n=0 := by
    unfold proj
    rw [sub_mul, one_mul, averaging_square hn0, sub_self]
  rw [base_split T hn2, mul_add, Matrix.mul_smul, hz, smul_zero, zero_add,
    Matrix.mul_smul, Matrix.smul_mul]
  rw [norm_smul, norm_inv]
  have hc : ‖(n:ℂ)-1‖ = (n:ℝ)-1 := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hden]
  rw [hc]
  calc
    _ ≤ ((n:ℝ)-1)⁻¹ * ‖castMatrix (signMatrix T)-1‖ :=
      mul_le_mul_of_nonneg_left (compress_norm hn0 _) (inv_nonneg.mpr hden.le)
    _ ≤ ((n:ℝ)-1)⁻¹ * ((n:ℝ)*(17/24)+1) :=
      mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add hs hid)) (inv_nonneg.mpr hden.le)
    _ ≤ 19/23 := by
      rw [inv_mul_eq_div]
      apply (div_le_iff₀ hden).mpr
      nlinarith

lemma actual_error_frobenius (T : Tournament n) (hn : 2 ≤ n) {a0 : ℝ}
    (h0 : 0 ≤ a0) (h1 : a0 < 1) (ha : ∀ i, |normalizedScore T i| ≤ a0) :
    ‖castMatrix (normalizedMatrix T)-castMatrix (baseMatrix T)‖ ≤
      Real.sqrt (errorBudget T a0) := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  apply (MatrixEuclideanEntryBound.operator_le_frobenius _).trans
  unfold MatrixEuclideanEntryBound.frobenius
  apply Real.sqrt_le_sqrt
  have hh := normalized_frobenius_bound T hn h0 h1 ha
  simpa [errorBudget, castMatrix, ComplexifiedSkewBound.complexify,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hh

/-- Same actual normalized matrix as normalized_frobenius_bound. -/
theorem actual_normalized_center_bound (T : Tournament n) (hn : 24 ≤ n) {a0 : ℝ}
    (h0 : 0 ≤ a0) (h1 : a0 < 1) (ha : ∀ i, |normalizedScore T i| ≤ a0) :
    ‖proj n*castMatrix (normalizedMatrix T)*proj n‖ ≤
      19/23+Real.sqrt (errorBudget T a0) := by
  have he : proj n*castMatrix (normalizedMatrix T)*proj n =
      proj n*castMatrix (baseMatrix T)*proj n +
      proj n*(castMatrix (normalizedMatrix T)-castMatrix (baseMatrix T))*proj n := by
    noncomm_ring
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add (base_center_bound T hn)
    ((compress_norm (by omega) _).trans (actual_error_frobenius T (by omega) h0 h1 ha)))

theorem actual_fixed_gap (T : Tournament n) (hn : 24 ≤ n) {a0 : ℝ}
    (h0 : 0 ≤ a0) (h1 : a0 < 1) (ha : ∀ i, |normalizedScore T i| ≤ a0)
    (hsmall : Real.sqrt (errorBudget T a0) ≤ 1/46) :
    ‖proj n*castMatrix (normalizedMatrix T)*proj n‖ ≤ 39/46 := by
  have hh := actual_normalized_center_bound T hn h0 h1 ha
  linarith
end ActualNormalizedCenteredGapCandidate
