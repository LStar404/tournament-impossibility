import AffineDeterminantEvaluationCandidate
import Mathlib
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.typeDecidableEq
set_option maxHeartbeats 1000000
namespace PositiveBranchEvaluationCandidate
open Matrix WeightedCoefficientNorm FormalSeriesDerivativeAtOne AffineDeterminantEvaluationCandidate
open scoped Matrix.Norms.L2Operator
variable {I : Type*} [Fintype I]
def complexify (Q : Matrix I I ℝ) : Matrix I I ℂ := Q.map Complex.ofRealHom
lemma det_complexify (Q : Matrix I I ℝ) (t : ℝ) :
    (1+(t:ℂ) • complexify Q).det=(((1+t • Q).det:ℝ):ℂ) := by
  change _ = Complex.ofRealHom ((1+t • Q).det)
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [complexify,Matrix.map_apply,Matrix.add_apply,Matrix.smul_apply,Matrix.one_apply,apply_ite]
lemma det_one_sub_positive (K : Matrix I I ℝ) (hK : ‖K‖<1) : 0<(1-K).det := by
  let f : ℝ → ℝ := fun t => (1-t • K).det
  have hc : Continuous f := by unfold f; fun_prop
  have hn (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) : f t≠0 := by
    have hnorm : ‖t • K‖≤‖K‖ := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
      exact mul_le_of_le_one_left (norm_nonneg K) ht.2
    exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
      (isUnit_one_sub_of_norm_lt_one (hnorm.trans_lt hK)))
  by_contra h
  have hle : f 1≤0 := by simpa [f] using le_of_not_gt h
  obtain ⟨t,ht,he⟩ := intermediate_value_Icc' (show (0:ℝ)≤1 by norm_num)
    hc.continuousOn (show (0:ℝ)∈Set.Icc (f 1) (f 0) from ⟨hle,by simp [f]⟩)
  exact hn t ht he
lemma affine_det_positive (Q : Matrix I I ℝ) (hQ : ‖Q‖<1)
    (t : ℝ) (ht : t∈Set.Icc (0:ℝ) 1) : 0<(1+t • Q).det := by
  have hn : ‖-(t • Q)‖<1 := by
    rw [norm_neg,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg Q) ht.2).trans_lt hQ
  simpa only [sub_neg_eq_add] using det_one_sub_positive (-(t • Q)) hn
lemma square_real_nonzero (z : ℂ) (d : ℝ) (hd : 0<d) (hz : z^2*(d:ℂ)=1) :
    z.im=0 ∧ z.re≠0 := by
  have hr := congrArg Complex.re hz
  have hi := congrArg Complex.im hz
  simp only [pow_two,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    mul_zero,zero_mul,add_zero,sub_zero,Complex.one_re,Complex.one_im] at hr hi
  have hprod : z.re*z.im=0 := by nlinarith
  have hre : z.re≠0 := by
    intro he
    rw [he] at hr
    nlinarith [sq_nonneg z.im]
  exact ⟨(mul_eq_zero.mp hprod).resolve_left hre,hre⟩
lemma eval_zero (F : PowerSeries ℂ) : eval F 0=F.constantCoeff := by
  unfold eval
  rw [tsum_eq_single 0]
  · simp
  · intro k hk
    simp [zero_pow hk]
lemma eval_continuous_at {rho : ℝ} (hr : 1<rho) (F : PowerSeries ℂ)
    (hF : Finite rho F) (z : ℂ) (hz : ‖z‖≤1) : ContinuousAt (eval F) z := by
  have hm : 1≤(1+rho)/2 := by linarith
  have hmr : (1+rho)/2<rho := by linarith
  have hz' : z∈Metric.ball (0:ℂ) ((1+rho)/2) := by
    simp only [Metric.mem_ball,dist_zero_right]
    linarith
  have hh := (derivative_sum hm hmr F hF 0 hz').continuousAt
  have he : derivativeSum F 0=eval F := by
    funext w
    simp [derivativeSum,term,eval]
  rw [he] at hh
  exact hh
lemma square_eval_real (Q : Matrix I I ℝ) (hQ : ‖Q‖<1)
    (F : PowerSeries ℂ) {rho : ℝ} (hr : 1<rho) (hF : Finite rho F)
    (hs : F^2*(affineSeries (complexify Q)).det=1)
    (t : ℝ) (ht : t∈Set.Icc (0:ℝ) 1) :
    (eval F (t:ℂ)).im=0 ∧ (eval F (t:ℂ)).re≠0 := by
  have hnorm : ‖(t:ℂ)‖≤rho := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht.1]
    linarith [ht.2]
  have hh := eval_square_identity (complexify Q) F (by linarith) hF hs (t:ℂ) hnorm
  rw [det_complexify] at hh
  exact square_real_nonzero _ _ (affine_det_positive Q hQ t ht) hh
lemma positive_at_one (Q : Matrix I I ℝ) (hQ : ‖Q‖<1)
    (F : PowerSeries ℂ) {rho : ℝ} (hr : 1<rho) (hF : Finite rho F)
    (hs : F^2*(affineSeries (complexify Q)).det=1) (h0 : F.constantCoeff=1) :
    0<(eval F 1).re := by
  let u : ℝ → ℝ := fun t => (eval F (t:ℂ)).re
  have hc : ContinuousOn u (Set.Icc (0:ℝ) 1) := by
    intro t ht
    have hz : ‖(t:ℂ)‖≤1 := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht.1]; exact ht.2
    exact (Complex.continuous_re.continuousAt.comp
      ((eval_continuous_at hr F hF (t:ℂ) hz).comp Complex.continuous_ofReal.continuousAt)).continuousWithinAt
  have hu0 : u 0=1 := by simp [u,eval_zero,h0]
  have hn t ht : u t≠0 := (square_eval_real Q hQ F hr hF hs t ht).2
  by_contra h
  have hle : u 1≤0 := by simpa [u] using le_of_not_gt h
  obtain ⟨t,ht,he⟩ := intermediate_value_Icc' (show (0:ℝ)≤1 by norm_num) hc
    (show (0:ℝ)∈Set.Icc (u 1) (u 0) from ⟨hle,by rw [hu0]; norm_num⟩)
  exact hn t ht he
 theorem positive_sqrt_endpoint (Q : Matrix I I ℝ) (hQ : ‖Q‖<1)
    (F : PowerSeries ℂ) {rho : ℝ} (hr : 1<rho) (hF : Finite rho F)
    (hs : F^2*(affineSeries (complexify Q)).det=1) (h0 : F.constantCoeff=1) :
    eval F 1=((Real.sqrt (1+Q).det)⁻¹:ℝ) := by
  have hd : 0<(1+Q).det := by simpa using affine_det_positive Q hQ 1 (by norm_num)
  have hsqrt := Real.sq_sqrt hd.le
  have hsp := Real.sqrt_pos.mpr hd
  have hp := positive_at_one Q hQ F hr hF hs h0
  have him := (square_eval_real Q hQ F hr hF hs 1 (by norm_num)).1
  have he := eval_square_identity (complexify Q) F (by linarith) hF hs 1 (by simpa using hr.le)
  have hre := congrArg Complex.re he
  rw [show (1:ℂ)=(1:ℝ) by norm_num,det_complexify] at hre
  simp only [one_smul,pow_two,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.one_re,him,mul_zero,zero_mul,add_zero,sub_zero] at hre
  norm_num only [Complex.ofReal_one] at him hre
  have hp2 : ((eval F 1).re*Real.sqrt (1+Q).det)^2=1 := by
    rw [mul_pow,hsqrt]
    nlinarith [hre]
  have hprod : (eval F 1).re*Real.sqrt (1+Q).det=1 := by
    nlinarith [mul_pos hp hsp]
  apply Complex.ext
  · simp only [Complex.ofReal_re]
    rw [←one_div]
    exact (eq_div_iff hsp.ne').mpr hprod
  · simpa using him
end PositiveBranchEvaluationCandidate

#print axioms PositiveBranchEvaluationCandidate.complexify
#check PositiveBranchEvaluationCandidate.complexify

#print axioms PositiveBranchEvaluationCandidate.det_complexify
#check PositiveBranchEvaluationCandidate.det_complexify

#print axioms PositiveBranchEvaluationCandidate.det_one_sub_positive
#check PositiveBranchEvaluationCandidate.det_one_sub_positive

#print axioms PositiveBranchEvaluationCandidate.affine_det_positive
#check PositiveBranchEvaluationCandidate.affine_det_positive

#print axioms PositiveBranchEvaluationCandidate.square_real_nonzero
#check PositiveBranchEvaluationCandidate.square_real_nonzero

#print axioms PositiveBranchEvaluationCandidate.eval_zero
#check PositiveBranchEvaluationCandidate.eval_zero

#print axioms PositiveBranchEvaluationCandidate.eval_continuous_at
#check PositiveBranchEvaluationCandidate.eval_continuous_at

#print axioms PositiveBranchEvaluationCandidate.square_eval_real
#check PositiveBranchEvaluationCandidate.square_eval_real

#print axioms PositiveBranchEvaluationCandidate.positive_at_one
#check PositiveBranchEvaluationCandidate.positive_at_one

#print axioms PositiveBranchEvaluationCandidate.positive_sqrt_endpoint
#check PositiveBranchEvaluationCandidate.positive_sqrt_endpoint
