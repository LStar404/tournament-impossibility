import SkewGaussianBaselineCandidate
import RealIndependentRestrictionCandidate

/-! Verified isolated integration. Only the original
tournament matrix supplies a spectral input, and its norm cap is proved.
Independent row/column deletions and both centering projections are contractions.
This file does not perform same-root scaling and does not eliminate any Γ term. -/
set_option autoImplicit false
noncomputable section
namespace ActualDeletedCenteredGaussianCandidate
open Matrix Finset
open TournamentHamiltonian ActualTournamentPrescalingBounds TournamentPrescalingMassBound
open IndependentCenteringEnergyCandidate RealProjectionAggregationCandidate
open ActualTwoSidedCenteringCandidate RealIndependentRestrictionCandidate
open SkewBaselineGramDifferenceCandidate
open scoped Matrix.Norms.L2Operator BigOperators
variable {n m : ℕ}

def retainedEmbedding (I : Finset (Fin n)) (r : Fin m ≃ {i // i ∈ Iᶜ}) :
    Fin m ↪ Fin n :=
  ⟨fun i => (r i).val, fun _ _ h => r.injective (Subtype.ext h)⟩

lemma signMatrix_transpose (T : Tournament n) : (signMatrix T)ᵀ = -signMatrix T := by
  ext i j
  exact signMatrix_skew T j i

lemma signMatrix_abs (T : Tournament n) (i j : Fin n) : |signMatrix T i j| ≤ 1 := by
  simp only [signMatrix]
  split_ifs <;> norm_num

/-- Exact equality, including the diagonal shift and the denominator n-1. -/
lemma realZ_eq_shifted (T : Tournament n) : realZ T = shifted (signMatrix T) := by
  ext i j
  simp only [realZ, shifted, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply,
    smul_eq_mul, div_eq_mul_inv]
  ring

lemma g_eq_gaussianLog {r c : ℕ} (Z : Matrix (Fin r) (Fin c) ℝ) :
    g Z = PositiveGramLogDetCandidate.gaussianLog (Zᵀ*Z) := rfl

theorem actual_Z_norm (T : Tournament n) (hn : 24 ≤ n) : ‖realZ T‖ ≤ 18/23 := by
  rw [realZ_eq_shifted]
  exact SkewGaussianActualNormCandidate.shifted_norm_bound hn (signMatrix T)
    (signMatrix_transpose T) (signMatrix_abs T)

lemma independent_restriction_contraction (Z : Matrix (Fin n) (Fin n) ℝ)
    (e f : Fin m ↪ Fin n) : ‖Z.submatrix e f‖ ≤ ‖Z‖ := by
  rw [← selection_submatrix]
  calc
    _ ≤ ‖(select e)ᵀ*Z‖*‖select f‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ ‖Z‖*1 := mul_le_mul (restriction_operator Z e) (select_norm f)
      (norm_nonneg _) (norm_nonneg _)
    _ = ‖Z‖ := mul_one _

theorem actual_restriction_norm (T : Tournament n) (hn : 24 ≤ n)
    (e f : Fin m ↪ Fin n) : ‖(realZ T).submatrix e f‖ ≤ 18/23 :=
  (independent_restriction_contraction (realZ T) e f).trans (actual_Z_norm T hn)

lemma centering_operator_contraction (hm : 0 < m) (Z : Matrix (Fin m) (Fin m) ℝ) :
    ‖center m*Z*center m‖ ≤ ‖Z‖ := by
  have hp := RealGramEndpoint.projection_norm (center m) (center_symmetric m) (center_square hm)
  have hl := projection_operator_contraction Z (center m) (center_symmetric m) (center_square hm)
  calc
    _ ≤ ‖center m*Z‖*‖center m‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ ‖Z‖*1 := mul_le_mul hl hp (norm_nonneg _) (norm_nonneg _)
    _ = ‖Z‖ := mul_one _

theorem actual_centered_restriction_norm (T : Tournament n) (hn : 24 ≤ n)
    (hm : 0 < m) (e f : Fin m ↪ Fin n) :
    ‖center m*((realZ T).submatrix e f)*center m‖ ≤ 18/23 :=
  (centering_operator_contraction hm _).trans (actual_restriction_norm T hn e f)

theorem actual_centered_det_pos (T : Tournament n) (hn : 24 ≤ n)
    (hm : 0 < m) (e f : Fin m ↪ Fin n) :
    let W := center m*((realZ T).submatrix e f)*center m
    0 < (1-Wᵀ*W).det := by
  dsimp only
  apply PositiveGramLogDetCandidate.det_one_sub_pos
  exact (SkewGaussianFactorCandidate.gram_norm_le_square _ (18/23) (by norm_num)
    (actual_centered_restriction_norm T hn hm e f)).trans_lt (by norm_num)

lemma retained_card_relation (I : Finset (Fin n))
    (r : Fin m ≃ {i // i ∈ Iᶜ}) (t : ℕ) (hI : I.card = t) : n = m+t := by
  have hc : (Iᶜ).card = m := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using (Fintype.card_congr r).symm
  have hh := (Finset.card_compl_add_card I).symm
  simpa only [Fintype.card_fin, hc, hI] using hh

theorem actual_baseline_g_bound (T : Tournament n) (hn : 24 ≤ n) :
    ‖g (realZ T)-g (scaled (signMatrix T))‖ ≤ 19/(n:ℝ) := by
  simp only [g_eq_gaussianLog, realZ_eq_shifted]
  exact (SkewGaussianBaselineCandidate.actual_gaussian_baseline hn (signMatrix T)
    (signMatrix_transpose T) (signMatrix_abs T)).2.2

/-- The previous deletion theorem's operator-gap hypothesis is discharged. -/
theorem actual_deletion_no_gap (T : Tournament n) (hn : 24 ≤ n)
    (e f : Fin m ↪ Fin n) (t : ℕ) (hcard : n = m+t) :
    ‖g ((realZ T).submatrix e f)-g (realZ T)‖ ≤
      ((t:ℝ)*((n:ℝ)+(m:ℝ))/((n:ℝ)-1)^2)/(2*(1-(18/23:ℝ)^2)) :=
  actual_deletion_g_bound T e f t hcard (18/23) (by norm_num) (by norm_num)
    (actual_Z_norm T hn)

/-- Equal deletion sizes do not require I=J, shared enumerations, or skewness
of the retained matrix. The previous retained-gap hypothesis is discharged. -/
theorem actual_centering_no_gap (T : Tournament n) (hn : 24 ≤ n) (hm : 0 < m)
    (I J : Finset (Fin n)) (r : Fin m ≃ {i // i ∈ Iᶜ}) (c : Fin m ≃ {j // j ∈ Jᶜ})
    (t : ℕ) (hI : I.card = t) (hJ : J.card = t) :
    let Z := (realZ T).submatrix (retainedEmbedding I r) (retainedEmbedding J c)
    ‖g (center m*Z*center m)-g Z‖ ≤
      (4*tau (normalizedScore T)+4*(n:ℝ)/((n:ℝ)-1)^2+
        4*(m:ℝ)*(t:ℝ)^2/((n:ℝ)-1)^2)/(2*(m:ℝ)*(1-(18/23:ℝ)^2)) := by
  dsimp only
  have hgap := actual_restriction_norm T hn (retainedEmbedding I r) (retainedEmbedding J c)
  have hh := actual_centering_g_bound T (by omega) hm I J r c
    (18/23) (by norm_num) (by norm_num) hgap
  dsimp only at hh
  rw [hI, hJ] at hh
  convert hh using 1 <;> first | rfl | ring

/-- Finite three-step comparison: skew baseline, independent deletion,
and two-sided centering. No additional operator-gap hypothesis remains. -/
theorem actual_independent_centered_total (T : Tournament n) (hn : 24 ≤ n) (hm : 0 < m)
    (I J : Finset (Fin n)) (r : Fin m ≃ {i // i ∈ Iᶜ}) (c : Fin m ≃ {j // j ∈ Jᶜ})
    (t : ℕ) (hI : I.card = t) (hJ : J.card = t) :
    let Z := (realZ T).submatrix (retainedEmbedding I r) (retainedEmbedding J c)
    ‖g (center m*Z*center m)-g (scaled (signMatrix T))‖ ≤
      19/(n:ℝ)+
      ((t:ℝ)*((n:ℝ)+(m:ℝ))/((n:ℝ)-1)^2)/(2*(1-(18/23:ℝ)^2))+
      (4*tau (normalizedScore T)+4*(n:ℝ)/((n:ℝ)-1)^2+
        4*(m:ℝ)*(t:ℝ)^2/((n:ℝ)-1)^2)/(2*(m:ℝ)*(1-(18/23:ℝ)^2)) := by
  dsimp only
  let Z := (realZ T).submatrix (retainedEmbedding I r) (retainedEmbedding J c)
  have hb := actual_baseline_g_bound T hn
  have hd := actual_deletion_no_gap T hn (retainedEmbedding I r) (retainedEmbedding J c)
    t (retained_card_relation I r t hI)
  have hc := actual_centering_no_gap T hn hm I J r c t hI hJ
  calc
    _ ≤ ‖g (center m*Z*center m)-g Z‖+‖g Z-g (scaled (signMatrix T))‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖g (center m*Z*center m)-g Z‖+
        (‖g Z-g (realZ T)‖+‖g (realZ T)-g (scaled (signMatrix T))‖) :=
      add_le_add le_rfl (norm_sub_le_norm_sub_add_norm_sub _ _ _)
    _ ≤ _ := add_le_add hc (add_le_add hd hb)
    _ = _ := by ring

/-- A user-supplied scalar τ upper bound replaces the actual score energy.
It is not a spectral assumption. All retained and centered gaps are derived. -/
theorem actual_independent_centered_total_of_tau_le (T : Tournament n)
    (hn : 24 ≤ n) (hm : 0 < m) (I J : Finset (Fin n))
    (r : Fin m ≃ {i // i ∈ Iᶜ}) (c : Fin m ≃ {j // j ∈ Jᶜ})
    (t : ℕ) (hI : I.card = t) (hJ : J.card = t)
    (U : ℝ) (hτ : tau (normalizedScore T) ≤ U) :
    let Z := (realZ T).submatrix (retainedEmbedding I r) (retainedEmbedding J c)
    ‖g (center m*Z*center m)-g (scaled (signMatrix T))‖ ≤
      19/(n:ℝ)+
      ((t:ℝ)*((n:ℝ)+(m:ℝ))/((n:ℝ)-1)^2)/(2*(1-(18/23:ℝ)^2))+
      (4*U+4*(n:ℝ)/((n:ℝ)-1)^2+
        4*(m:ℝ)*(t:ℝ)^2/((n:ℝ)-1)^2)/(2*(m:ℝ)*(1-(18/23:ℝ)^2)) := by
  dsimp only
  apply (actual_independent_centered_total T hn hm I J r c t hI hJ).trans
  apply add_le_add le_rfl
  apply div_le_div_of_nonneg_right
  · linarith
  · exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (by norm_num)

end ActualDeletedCenteredGaussianCandidate
