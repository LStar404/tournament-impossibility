import QuadraticGramDerivative
set_option autoImplicit false
noncomputable section
namespace GaussianDisplacement
open Matrix RealGramEndpoint RealBilinearTrace QuadraticGramDerivative PositiveGramLogDetCandidate
open scoped Matrix.Norms.L2Operator BigOperators
variable {r c : ℕ}
lemma line_convex (U V : Matrix (Fin r) (Fin c) ℝ) (t : ℝ) :
    line U (V-U) t = (1-t) • U+t • V := by
  simp only [line, smul_sub, sub_smul, one_smul]
  abel
lemma line_norm (U V : Matrix (Fin r) (Fin c) ℝ) (q t : ℝ)
    (hU : ‖U‖ ≤ q) (hV : ‖V‖ ≤ q) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖line U (V-U) t‖ ≤ q := by
  rw [line_convex]
  calc
    _ ≤ ‖(1-t) • U‖+‖t • V‖ := norm_add_le _ _
    _ = (1-t)*‖U‖+t*‖V‖ := by rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr ht1),abs_of_nonneg ht]
    _ ≤ (1-t)*q+t*q := add_le_add (mul_le_mul_of_nonneg_left hU (sub_nonneg.mpr ht1))
      (mul_le_mul_of_nonneg_left hV ht)
    _ = q := by ring
lemma line_fnorm (U V : Matrix (Fin r) (Fin c) ℝ) (F t : ℝ)
    (hU : fnorm U ≤ F) (hV : fnorm V ≤ F) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    fnorm (line U (V-U) t) ≤ F := by
  rw [line_convex]
  calc
    _ ≤ fnorm ((1-t) • U)+fnorm (t • V) := fnorm_add _ _
    _ = (1-t)*fnorm U+t*fnorm V := by rw [fnorm_smul,fnorm_smul,
      abs_of_nonneg (sub_nonneg.mpr ht1),abs_of_nonneg ht]
    _ ≤ (1-t)*F+t*F := add_le_add (mul_le_mul_of_nonneg_left hU (sub_nonneg.mpr ht1))
      (mul_le_mul_of_nonneg_left hV ht)
    _ = F := by ring
lemma gram_norm (W : Matrix (Fin r) (Fin c) ℝ) (q : ℝ) (hq : 0 ≤ q) (hW : ‖W‖ ≤ q) :
    ‖Wᵀ*W‖ ≤ q^2 := by
  calc
    _ ≤ ‖Wᵀ‖*‖W‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ q*q := by rw [← Matrix.conjTranspose_eq_transpose_of_trivial W, Matrix.l2_opNorm_conjTranspose]; gcongr
    _ = _ := by ring
lemma gram_det_pos (W : Matrix (Fin r) (Fin c) ℝ) (q : ℝ)
    (hq : 0 ≤ q) (hq1 : q < 1) (hW : ‖W‖ ≤ q) : 0 < (1-Wᵀ*W).det :=
  det_one_sub_pos _ ((gram_norm W q hq hW).trans_lt (by nlinarith))
lemma derivative_bound (W D : Matrix (Fin r) (Fin c) ℝ) (q F : ℝ)
    (hq : 0 ≤ q) (hq1 : q < 1) (hW : ‖W‖ ≤ q) (hF : fnorm W ≤ F) :
    ‖((1-Wᵀ*W)⁻¹ * (-(Dᵀ*W+Wᵀ*D))).trace‖ ≤ 2*F*fnorm D/(1-q^2) := by
  let R := (1-Wᵀ*W)⁻¹
  have hi : ‖R‖ ≤ 1/(1-q^2) := (RealGramEndpoint.inverse_bound _ _ (gram_norm W q hq hW) (by nlinarith)).2
  have hd : 0 ≤ fnorm D := norm_nonneg _
  have hw : 0 ≤ fnorm W := norm_nonneg _
  have hf : 0 ≤ F := hw.trans hF
  have hg : 0 ≤ 1/(1-q^2) := le_of_lt (one_div_pos.mpr (by nlinarith))
  rw [Matrix.mul_neg, Matrix.trace_neg, norm_neg, Matrix.mul_add, Matrix.trace_add]
  calc
    _ ≤ ‖(R*(Dᵀ*W)).trace‖+‖(R*(Wᵀ*D)).trace‖ := norm_add_le _ _
    _ ≤ ‖R‖*fnorm D*fnorm W+‖R‖*fnorm W*fnorm D := add_le_add (bilinear_trace D W R) (bilinear_trace W D R)
    _ ≤ (1/(1-q^2))*fnorm D*F+(1/(1-q^2))*F*fnorm D := by gcongr
    _ = _ := by ring
/-- Actual logdet endpoint; all derivative and nonsingularity inputs are derived. -/
theorem logdet_lipschitz (U V : Matrix (Fin r) (Fin c) ℝ) (q F : ℝ)
    (hq : 0 ≤ q) (hq1 : q < 1) (hU : ‖U‖ ≤ q) (hV : ‖V‖ ≤ q)
    (hFU : fnorm U ≤ F) (hFV : fnorm V ≤ F) :
    ‖Real.log (1-Vᵀ*V).det-Real.log (1-Uᵀ*U).det‖ ≤ 2*F*fnorm (V-U)/(1-q^2) := by
  have hd (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :=
    (logdet_hasDerivAt U (V-U) t (gram_det_pos _ q hq hq1
      (line_norm U V q t hU hV ht.1 ht.2)).ne').hasDerivWithinAt (s:=Set.Icc (0:ℝ) 1)
  have hb (t : ℝ) (ht : t ∈ Set.Ico (0:ℝ) 1) :=
    derivative_bound (line U (V-U) t) (V-U) q F hq hq1
      (line_norm U V q t hU hV ht.1 ht.2.le) (line_fnorm U V F t hFU hFV ht.1 ht.2.le)
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01' hd hb
  simpa [line] using h
/-- Positive Gaussian determinant interpretation and sharp half-scaled displacement bound. -/
theorem gaussian_lipschitz (U V : Matrix (Fin r) (Fin c) ℝ) (q F : ℝ)
    (hq : 0 ≤ q) (hq1 : q < 1) (hU : ‖U‖ ≤ q) (hV : ‖V‖ ≤ q)
    (hFU : fnorm U ≤ F) (hFV : fnorm V ≤ F) :
    0 < (1-Uᵀ*U).det ∧ 0 < (1-Vᵀ*V).det ∧
    ‖gaussianLog (Vᵀ*V)-gaussianLog (Uᵀ*U)‖ ≤ F*fnorm (V-U)/(1-q^2) := by
  refine ⟨gram_det_pos U q hq hq1 hU, gram_det_pos V q hq hq1 hV, ?_⟩
  have h := logdet_lipschitz U V q F hq hq1 hU hV hFU hFV
  have he : gaussianLog (Vᵀ*V)-gaussianLog (Uᵀ*U) =
      -(Real.log (1-Vᵀ*V).det-Real.log (1-Uᵀ*U).det)/2 := by unfold gaussianLog; ring
  rw [he, norm_div, norm_neg, show ‖(2:ℝ)‖=2 by norm_num]
  calc
    _ ≤ (2*F*fnorm (V-U)/(1-q^2))/2 := div_le_div_of_nonneg_right h (by norm_num)
    _ = _ := by ring
end GaussianDisplacement
