import ActualAffineLogDetCandidate
import Mathlib
set_option autoImplicit false
noncomputable section
namespace RealGramEndpoint
open Matrix WithLp
open scoped Matrix.Norms.L2Operator BigOperators InnerProductSpace
variable {r c : ℕ}
def frob (Z : Matrix (Fin r) (Fin c) ℝ) : ℝ := ∑ i, ∑ j, Z i j ^ 2
def loss (Z : Matrix (Fin r) (Fin c) ℝ) (P : Matrix (Fin r) (Fin r) ℝ) := Zᵀ*(1-P)*Z
def path (Z : Matrix (Fin r) (Fin c) ℝ) (P : Matrix (Fin r) (Fin r) ℝ) (s : ℝ) :=
  (1 : Matrix (Fin c) (Fin c) ℝ)-Zᵀ*((1-s) • (1 : Matrix (Fin r) (Fin r) ℝ)+s • P)*Z
lemma path_affine (Z : Matrix (Fin r) (Fin c) ℝ) (P : Matrix (Fin r) (Fin r) ℝ) (s : ℝ) :
    path Z P s = (1-Zᵀ*Z)+s • loss Z P := by
  simp only [path, loss, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, Matrix.mul_sub, Matrix.sub_mul, smul_sub, sub_smul, one_smul]
  abel
lemma loss_gram (Z : Matrix (Fin r) (Fin c) ℝ) (P : Matrix (Fin r) (Fin r) ℝ)
    (hP : Pᵀ=P) (hPP : P*P=P) : loss Z P = ((1-P)*Z)ᵀ*((1-P)*Z) := by
  have hc : (1-P)*(1-P)=1-P := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hPP, sub_self, sub_zero]
  simp only [loss, Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_one, hP]
  calc
    Zᵀ*(1-P)*Z = Zᵀ*((1-P)*(1-P))*Z := by rw [hc]
    _ = _ := by simp only [Matrix.mul_assoc]
lemma trace_bound (B : Matrix (Fin r) (Fin c) ℝ) (R : Matrix (Fin c) (Fin c) ℝ) :
    ‖(R*(Bᵀ*B)).trace‖ ≤ ‖R‖*frob B := by
  have row (i : Fin r) : ‖(B*R*Bᵀ) i i‖ ≤ ‖R‖ * ∑ j, B i j^2 := by
    let x := toLp 2 (fun j => B i j)
    have hh := norm_inner_le_norm (𝕜:=ℝ) x ((Matrix.toEuclideanCLM (𝕜:=ℝ) R) x)
    have hi : ⟪x, (Matrix.toEuclideanCLM (𝕜:=ℝ) R) x⟫_ℝ = (B*R*Bᵀ) i i := by
      rw [Matrix.mul_assoc]
      simp [x, EuclideanSpace.inner_eq_star_dotProduct, Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
    rw [hi] at hh
    calc
      _ ≤ ‖x‖ * ‖(Matrix.toEuclideanCLM (𝕜:=ℝ) R) x‖ := hh
      _ ≤ ‖x‖ * (‖Matrix.toEuclideanCLM (𝕜:=ℝ) R‖*‖x‖) :=
        mul_le_mul_of_nonneg_left ((Matrix.toEuclideanCLM (𝕜:=ℝ) R).le_opNorm x) (norm_nonneg _)
      _ = ‖R‖*∑ j, B i j^2 := by
        rw [Matrix.l2_opNorm_toEuclideanCLM]
        rw [show ‖x‖*(‖R‖*‖x‖)=‖R‖*‖x‖^2 by ring, EuclideanSpace.real_norm_sq_eq]
  have ht : (R*(Bᵀ*B)).trace = (B*R*Bᵀ).trace := by
    rw [Matrix.trace_mul_cycle', Matrix.mul_assoc]
  rw [ht]
  calc
    _ ≤ ∑ i, ‖(B*R*Bᵀ) i i‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖R‖*∑ j, B i j^2 := Finset.sum_le_sum fun i _ => row i
    _ = _ := by rw [← Finset.mul_sum]; rfl
lemma projection_norm (P : Matrix (Fin r) (Fin r) ℝ) (hP : Pᵀ=P) (hPP : P*P=P) : ‖P‖ ≤ 1 := by
  apply IsStarProjection.norm_le
  apply (isStarProjection_iff').mpr
  exact ⟨hPP, by simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using hP⟩
lemma kernel_norm (Z : Matrix (Fin r) (Fin c) ℝ) (P : Matrix (Fin r) (Fin r) ℝ)
    (hP : Pᵀ=P) (hPP : P*P=P) (s q : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hq : 0 ≤ q) (hZ : ‖Z‖ ≤ q) :
    ‖Zᵀ*((1-s) • (1 : Matrix (Fin r) (Fin r) ℝ)+s • P)*Z‖ ≤ q^2 := by
  have hI : ‖(1 : Matrix (Fin r) (Fin r) ℝ)‖ ≤ 1 := by
    rw [← Matrix.l2_opNorm_toEuclideanCLM, map_one]
    exact ContinuousLinearMap.norm_id_le
  have hQ : ‖(1-s) • (1 : Matrix (Fin r) (Fin r) ℝ)+s • P‖ ≤ 1 := by
    calc
      _ ≤ ‖(1-s) • (1 : Matrix (Fin r) (Fin r) ℝ)‖+‖s • P‖ := norm_add_le _ _
      _ = (1-s)*‖(1 : Matrix (Fin r) (Fin r) ℝ)‖+s*‖P‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (sub_nonneg.mpr hs1), abs_of_nonneg hs]
      _ ≤ (1-s)*1+s*1 := add_le_add (mul_le_mul_of_nonneg_left hI (sub_nonneg.mpr hs1))
        (mul_le_mul_of_nonneg_left (projection_norm P hP hPP) hs)
      _ = 1 := by ring
  calc
    _ ≤ (‖Zᵀ‖*‖(1-s) • (1 : Matrix (Fin r) (Fin r) ℝ)+s • P‖)*‖Z‖ :=
      (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ (q*1)*q := by
      rw [← Matrix.conjTranspose_eq_transpose_of_trivial Z, Matrix.l2_opNorm_conjTranspose]
      gcongr
    _ = q^2 := by ring
lemma inverse_bound (K : Matrix (Fin c) (Fin c) ℝ) (q : ℝ) (hK : ‖K‖ ≤ q) (hq : q < 1) :
    IsUnit (1-K) ∧ ‖(1-K)⁻¹‖ ≤ 1/(1-q) := by
  have hsmall : ‖K‖ < 1 := hK.trans_lt hq
  refine ⟨isUnit_one_sub_of_norm_lt_one hsmall, ?_⟩
  have h := tsum_geometric_le_of_norm_lt_one K hsmall
  rw [geom_series_eq_inverse _ hsmall, ← Matrix.nonsing_inv_eq_ringInverse] at h
  have hI : ‖(1 : Matrix (Fin c) (Fin c) ℝ)‖ ≤ 1 := by
    rw [← Matrix.l2_opNorm_toEuclideanCLM, map_one]
    exact ContinuousLinearMap.norm_id_le
  have hinv : (1-‖K‖)⁻¹ ≤ (1-q)⁻¹ := inv_anti₀ (by linarith) (by linarith)
  rw [one_div]
  linarith
lemma path_inverse (Z : Matrix (Fin r) (Fin c) ℝ) (P : Matrix (Fin r) (Fin r) ℝ)
    (hP : Pᵀ=P) (hPP : P*P=P) (s q : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hq : 0 ≤ q) (hq1 : q < 1) (hZ : ‖Z‖ ≤ q) :
    IsUnit (path Z P s) ∧ ‖(path Z P s)⁻¹‖ ≤ 1/(1-q^2) :=
  inverse_bound _ _ (kernel_norm Z P hP hPP s q hs hs1 hq hZ) (by nlinarith)
lemma path_det_ne_zero (Z : Matrix (Fin r) (Fin c) ℝ) (P : Matrix (Fin r) (Fin r) ℝ)
    (hP : Pᵀ=P) (hPP : P*P=P) (s q : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hq : 0 ≤ q) (hq1 : q < 1) (hZ : ‖Z‖ ≤ q) : (path Z P s).det ≠ 0 := by
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
    (path_inverse Z P hP hPP s q hs hs1 hq hq1 hZ).1)
lemma path_trace_bound (Z : Matrix (Fin r) (Fin c) ℝ) (P : Matrix (Fin r) (Fin r) ℝ)
    (hP : Pᵀ=P) (hPP : P*P=P) (s q : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hq : 0 ≤ q) (hq1 : q < 1) (hZ : ‖Z‖ ≤ q) :
    ‖((path Z P s)⁻¹*loss Z P).trace‖ ≤ frob ((1-P)*Z)/(1-q^2) := by
  rw [loss_gram Z P hP hPP]
  have hf : 0 ≤ frob ((1-P)*Z) := by unfold frob; positivity
  calc
    _ ≤ ‖(path Z P s)⁻¹‖*frob ((1-P)*Z) := trace_bound _ _
    _ ≤ (1/(1-q^2))*frob ((1-P)*Z) := mul_le_mul_of_nonneg_right
      (path_inverse Z P hP hPP s q hs hs1 hq hq1 hZ).2 hf
    _ = _ := by ring
lemma path_log_derivative (Z : Matrix (Fin r) (Fin c) ℝ) (P : Matrix (Fin r) (Fin r) ℝ)
    (s : ℝ) (hn : (path Z P s).det ≠ 0) :
    HasDerivAt (fun x : ℝ => Real.log (path Z P x).det) (((path Z P s)⁻¹*loss Z P).trace) s := by
  simp only [path_affine] at hn ⊢
  exact ActualAffineLogDetCandidate.hasDerivAt_log_det_affine _ _ _ hn
/-- General affine endpoint API: explicit nonsingularity and trace bound,
not an assumed derivative. Applicable beyond projection losses. -/
theorem affine_logdet_endpoint (A B : Matrix (Fin c) (Fin c) ℝ) (M : ℝ)
    (hn : ∀ s ∈ Set.Icc (0:ℝ) 1, (A+s • B).det ≠ 0)
    (hb : ∀ s ∈ Set.Ico (0:ℝ) 1, ‖((A+s • B)⁻¹*B).trace‖ ≤ M) :
    ‖Real.log (A+B).det-Real.log A.det‖ ≤ M := by
  have hd (s : ℝ) (hs : s ∈ Set.Icc (0:ℝ) 1) :=
    (ActualAffineLogDetCandidate.hasDerivAt_log_det_affine A B s (hn s hs)).hasDerivWithinAt
      (s:=Set.Icc (0:ℝ) 1)
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01' hd hb
  simpa only [one_smul, zero_smul, add_zero] using h
/-- Actual Real.log(Matrix.det) endpoint difference, derived by the mean value bound. -/
theorem logdet_endpoint (Z : Matrix (Fin r) (Fin c) ℝ) (P : Matrix (Fin r) (Fin r) ℝ)
    (hP : Pᵀ=P) (hPP : P*P=P) (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) (hZ : ‖Z‖ ≤ q) :
    ‖Real.log (1-Zᵀ*P*Z).det-Real.log (1-Zᵀ*Z).det‖ ≤ frob ((1-P)*Z)/(1-q^2) := by
  have hd (s : ℝ) (hs : s ∈ Set.Icc (0:ℝ) 1) :=
    (path_log_derivative Z P s (path_det_ne_zero Z P hP hPP s q hs.1 hs.2 hq hq1 hZ )).hasDerivWithinAt (s:=Set.Icc (0:ℝ) 1)
  have hb (s : ℝ) (hs : s ∈ Set.Ico (0:ℝ) 1) :=
    path_trace_bound Z P hP hPP s q hs.1 hs.2.le hq hq1 hZ
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01' hd hb
  simpa only [path, sub_self, zero_smul, one_smul, zero_add, sub_zero, add_zero, Matrix.mul_one] using h
end RealGramEndpoint
