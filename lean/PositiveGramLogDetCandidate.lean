import RealGramEndpoint
import Mathlib
/-! Isolated verified batch (2026-11-10). Positivity via actual determinant continuity and nonvanishing;
factorized Gram-difference absolute logdet endpoint. No spectral decomposition. -/
set_option autoImplicit false
noncomputable section
namespace PositiveGramLogDetCandidate
open Matrix RealGramEndpoint
open scoped Matrix.Norms.L2Operator BigOperators
variable {r c : ℕ}

lemma det_one_sub_pos (K : Matrix (Fin c) (Fin c) ℝ) (hK : ‖K‖ < 1) :
    0 < (1-K).det := by
  let f : ℝ → ℝ := fun t => (1-t • K).det
  have hc : Continuous f := by unfold f; fun_prop
  have hn (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) : f t ≠ 0 := by
    have hnorm : ‖t • K‖ ≤ ‖K‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact mul_le_of_le_one_left (norm_nonneg K) ht.2
    exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
      (RealGramEndpoint.inverse_bound (t • K) ‖K‖ hnorm hK).1)
  by_contra h
  have hle : f 1 ≤ 0 := by simpa [f] using (le_of_not_gt h)
  have hzero : (0:ℝ) ∈ Set.Icc (f 1) (f 0) := ⟨hle, by simp [f]⟩
  obtain ⟨t, ht, he⟩ := intermediate_value_Icc' (show (0:ℝ) ≤ 1 by norm_num)
    hc.continuousOn hzero
  exact hn t ht he

lemma convex_kernel_norm (K0 K1 : Matrix (Fin c) (Fin c) ℝ) (q t : ℝ)
    (h0 : ‖K0‖ ≤ q^2) (h1 : ‖K1‖ ≤ q^2) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖(1-t) • K0+t • K1‖ ≤ q^2 := by
  calc
    _ ≤ ‖(1-t) • K0‖+‖t • K1‖ := norm_add_le _ _
    _ = (1-t)*‖K0‖+t*‖K1‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr ht1), abs_of_nonneg ht]
    _ ≤ (1-t)*q^2+t*q^2 := add_le_add
      (mul_le_mul_of_nonneg_left h0 (sub_nonneg.mpr ht1))
      (mul_le_mul_of_nonneg_left h1 ht)
    _ = q^2 := by ring

lemma factor_path (K0 K1 : Matrix (Fin c) (Fin c) ℝ)
    (B : Matrix (Fin r) (Fin c) ℝ) (hB : K1-K0=Bᵀ*B) (t : ℝ) :
    (1-K0)+t • (-(Bᵀ*B)) = 1-((1-t) • K0+t • K1) := by
  rw [← hB]
  simp only [smul_neg, smul_sub, sub_smul, one_smul]
  abel

/-- Actual factorization is explicit. No generic PSD-to-factor theorem assumed. -/
theorem factor_logdet_bound (K0 K1 : Matrix (Fin c) (Fin c) ℝ)
    (B : Matrix (Fin r) (Fin c) ℝ) (hB : K1-K0=Bᵀ*B)
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (h0 : ‖K0‖ ≤ q^2) (h1 : ‖K1‖ ≤ q^2) :
    ‖Real.log (1-K1).det-Real.log (1-K0).det‖ ≤ frob B/(1-q^2) := by
  have hq2 : q^2 < 1 := by nlinarith
  have hn (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
      ((1-K0)+t • (-(Bᵀ*B))).det ≠ 0 := by
    rw [factor_path K0 K1 B hB]
    exact (det_one_sub_pos _ ((convex_kernel_norm K0 K1 q t h0 h1 ht.1 ht.2).trans_lt hq2)).ne'
  have hb (t : ℝ) (ht : t ∈ Set.Ico (0:ℝ) 1) :
      ‖((((1-K0)+t • (-(Bᵀ*B)))⁻¹)*(-(Bᵀ*B))).trace‖ ≤ frob B/(1-q^2) := by
    rw [factor_path K0 K1 B hB, Matrix.mul_neg, Matrix.trace_neg, norm_neg]
    have hi := (RealGramEndpoint.inverse_bound _ (q^2)
      (convex_kernel_norm K0 K1 q t h0 h1 ht.1 ht.2.le) hq2).2
    have hf : 0 ≤ frob B := by unfold frob; positivity
    calc
      _ ≤ ‖(1-((1-t) • K0+t • K1))⁻¹‖*frob B := trace_bound B _
      _ ≤ (1/(1-q^2))*frob B := mul_le_mul_of_nonneg_right hi hf
      _ = _ := by ring
  have h := affine_logdet_endpoint (1-K0) (-(Bᵀ*B)) (frob B/(1-q^2)) hn hb
  have he : (1-K0)+ -(Bᵀ*B)=1-K1 := by rw [← hB]; abel
  simpa only [he] using h

def gaussianLog (K : Matrix (Fin c) (Fin c) ℝ) : ℝ := -(Real.log (1-K).det)/2

/-- Positive determinants and the actual Gaussian-log half scaling. -/
theorem positive_gaussian_factor_bound (K0 K1 : Matrix (Fin c) (Fin c) ℝ)
    (B : Matrix (Fin r) (Fin c) ℝ) (hB : K1-K0=Bᵀ*B)
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (h0 : ‖K0‖ ≤ q^2) (h1 : ‖K1‖ ≤ q^2) :
    0 < (1-K0).det ∧ 0 < (1-K1).det ∧
    ‖gaussianLog K1-gaussianLog K0‖ ≤ frob B/(2*(1-q^2)) := by
  have hq2 : q^2 < 1 := by nlinarith
  refine ⟨det_one_sub_pos K0 (h0.trans_lt hq2), det_one_sub_pos K1 (h1.trans_lt hq2), ?_⟩
  have h := factor_logdet_bound K0 K1 B hB q hq hq1 h0 h1
  have he : gaussianLog K1-gaussianLog K0 =
      -(Real.log (1-K1).det-Real.log (1-K0).det)/2 := by unfold gaussianLog; ring
  rw [he, norm_div, norm_neg]
  rw [show ‖(2:ℝ)‖ = 2 by norm_num]
  calc
    _ ≤ (frob B/(1-q^2))/2 := div_le_div_of_nonneg_right h (by norm_num)
    _ = _ := by rw [div_div]; congr 1; ring
end PositiveGramLogDetCandidate
