import SkewGaussianFactorCandidate
import TournamentSkewMargin
import RawScalingSynthesis

/-! Isolated verified norm adapter. Existing real_gap_of_complex gives the genuine
real/complex Euclidean comparison. No entrywise default norm is used. -/
set_option autoImplicit false
noncomputable section
namespace SkewGaussianActualNormCandidate
open Matrix
open SkewBaselineGramDifferenceCandidate
open scoped Matrix.Norms.L2Operator BigOperators
variable {n : ℕ}

lemma skew_entries (S : Matrix (Fin n) (Fin n) ℝ) (hS : Sᵀ = -S) :
    ∀ i j, S j i = -S i j := by
  intro i j
  simpa only [Matrix.transpose_apply, Matrix.neg_apply] using congrFun (congrFun hS i) j

/-- Restrict the established complex Euclidean bound to real vectors. -/
theorem actual_skew_norm (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : Sᵀ = -S) (he : ∀ i j, |S i j| ≤ 1) :
    ‖S‖ ≤ (n:ℝ)*(17/24) := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  apply RawScalingSynthesis.real_gap_of_complex S (by positivity)
  have hc : ActualHessianComplex.realComplex S = ComplexifiedSkewBound.complexify S := rfl
  rw [hc]
  exact TournamentSkewMargin.unnormalized S (skew_entries S hS) he

lemma identity_norm_le : ‖(1 : Matrix (Fin n) (Fin n) ℝ)‖ ≤ 1 := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM, map_one]
  exact ContinuousLinearMap.norm_id_le

theorem scaled_norm_bound (hn : 0 < n) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : Sᵀ = -S) (he : ∀ i j, |S i j| ≤ 1) : ‖scaled S‖ ≤ 17/24 := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  unfold scaled
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hnR.le)]
  calc
    _ ≤ (n:ℝ)⁻¹*((n:ℝ)*(17/24)) :=
      mul_le_mul_of_nonneg_left (actual_skew_norm S hS he) (inv_nonneg.mpr hnR.le)
    _ = 17/24 := by rw [← mul_assoc, inv_mul_cancel₀ hnR.ne', one_mul]

theorem shifted_norm_bound (hn : 24 ≤ n) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : Sᵀ = -S) (he : ∀ i j, |S i j| ≤ 1) : ‖shifted S‖ ≤ 18/23 := by
  have hnR : (24:ℝ) ≤ n := by exact_mod_cast hn
  have hd : 0 < (n:ℝ)-1 := by linarith
  unfold shifted
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hd.le)]
  calc
    _ ≤ ((n:ℝ)-1)⁻¹*((n:ℝ)*(17/24)+1) :=
      mul_le_mul_of_nonneg_left
        ((norm_sub_le _ _).trans (add_le_add (actual_skew_norm S hS he) identity_norm_le))
        (inv_nonneg.mpr hd.le)
    _ ≤ 18/23 := by
      rw [inv_mul_eq_div]
      apply (div_le_iff₀ hd).mpr
      nlinarith

theorem actual_common_norm_caps (hn : 24 ≤ n) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : Sᵀ = -S) (he : ∀ i j, |S i j| ≤ 1) :
    ‖scaled S‖ ≤ 19/23 ∧ ‖shifted S‖ ≤ 19/23 := by
  constructor
  · exact (scaled_norm_bound (by omega) S hS he).trans (by norm_num)
  · exact (shifted_norm_bound hn S hS he).trans (by norm_num)

end SkewGaussianActualNormCandidate
