import GaussianSourceProduct
import ComplexResolventAnalytic

noncomputable section
open Filter Topology DiamondGap
namespace GaussianSourceAnalytic
open GaussianParameterBranch GaussianScalarFactor ActualGaussianSourceExponent
open ActualComplexScoreSource

lemma parameter_differentiableAt (n : ℕ) (z : ℂ) {r : ℝ}
    (hz : ‖z‖≤r) (hb : r^2/(n:ℝ)^2≤1/2) :
    DifferentiableAt ℂ (parameter n) z := by
  have hl := differentiableAt_logBeta n z hz hb
  have hroot : DifferentiableAt ℂ (root n) z := by
    unfold root
    exact (hl.neg.div_const 2).cexp
  exact differentiableAt_id.mul hroot

lemma prefactor_differentiableAt (n : ℕ) (z : ℂ) {r : ℝ}
    (hz : ‖z‖≤r) (hb : r^2/(n:ℝ)^2≤1/2) :
    DifferentiableAt ℂ (prefactor n) z := by
  have hl := differentiableAt_logBeta n z hz hb
  exact (((hl.const_mul (-(n:ℂ))).div_const 2).cexp)

lemma finiteKernel_differentiable (n : ℕ) : Differentiable ℂ (DiamondFreeKernelLimit.finiteKernel n) := by
  unfold DiamondFreeKernelLimit.finiteKernel
  fun_prop

/-- The true assembled functions are differentiable on a common disk. The
threshold is uniform in the graph and |v|<=1 and requires no energy bound. -/
theorem eventually_differentiable_disk {r R : ℝ} (hr : 0≤r) (hrR : r<R)
    (hpi : R<Real.pi/2) :
    ∀ᶠ n : ℕ in atTop, ∀ T : Tournament (Fin n), T.diamonds.card=0 →
      ∀ v : ℂ, ‖v‖≤1 →
        DifferentiableOn ℂ (GaussianSourceProduct.product T v) (Metric.ball 0 r) ∧
        DifferentiableOn ℂ (GaussianSourceProduct.target v) (Metric.ball 0 r) := by
  have hR : 0≤R := hr.trans hrR.le
  have hcosR : 0<Real.cos R := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos],hpi⟩
  filter_upwards [ComplexKernelDiskLower.eventually_thresholds hR hpi,
    ComplexResolventAnalytic.eventually_analytic_disk hR hpi,
    ActualGaussianSourceExponent.eventually_div_le r (1/2) (by norm_num),
    ActualGaussianSourceExponent.eventually_div_sq_le (r^2) (1/2) (by norm_num),
    ActualGaussianSourceExponent.eventually_div_sq_le (2*r^3) (R-r) (sub_pos.mpr hrR)]
    with n hn hs hsmall hb hgap
  intro T hT v hv
  have hpoint (z : ℂ) (hzball : z∈Metric.ball 0 r) :
      DifferentiableAt ℂ (GaussianSourceProduct.product T v) z ∧
      DifferentiableAt ℂ (GaussianSourceProduct.target v) z := by
    have hz : ‖z‖≤r := (by simpa using hzball : ‖z‖<r).le
    have hk := parameter_in_disk n z hz hb hgap
    have hkd := parameter_differentiableAt n z hz hb
    have hpd := prefactor_differentiableAt n z hz hb
    have hsource : DifferentiableAt ℂ (source T) (parameter n z) :=
      (hs T hT (parameter n z) (by simpa using hk)).differentiableAt
    have hsc := hsource.comp z hkd
    have hden : DifferentiableAt ℂ (fun t : ℂ => 1+v*t/(n:ℂ)) z := by fun_prop
    have hvz : ‖v*z‖≤r := by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right hv (norm_nonneg z)).trans (by simpa using hz)
    have hdennz := (GaussianSourceExponent.denominator_bound n hn.1 (v*z) hvz hsmall).2.1
    have hnum : DifferentiableAt ℂ (fun t : ℂ => v*t) z := by fun_prop
    have hexp : DifferentiableAt ℂ (actualExponent T v) z := by
      unfold actualExponent GaussianSourceExponent.exponent
      exact (hnum.div hden hdennz).sub
        (((hkd.pow 2).mul (hsc.div_const ((n:ℂ)^2))).div hden hdennz)
    have hkernel : DifferentiableAt ℂ
        (fun t => DiamondFreeKernelLimit.finiteKernel n (parameter n t*Complex.I)) z :=
      (finiteKernel_differentiable n _).comp z (hkd.mul_const Complex.I)
    have hklow := ComplexKernelDiskLower.finite_kernel_lower n hn.1 hR hpi
      hn.2.1 hn.2.2.1 hn.2.2.2 hk
    have hknz : DiamondFreeKernelLimit.finiteKernel n (parameter n z*Complex.I) ≠ 0 :=
      norm_pos_iff.mp ((by positivity : 0<Real.cos R/2).trans_le hklow)
    have hgauss : DifferentiableAt ℂ (gaussian n) z := hpd.div hkernel hknz
    have hcoslow := ComplexKernelDiskLower.cosine_lower hR hpi (hz.trans hrR.le)
    have hcosnz : Complex.cos z ≠ 0 := norm_pos_iff.mp (hcosR.trans_le hcoslow)
    constructor
    · exact hgauss.mul hexp.cexp
    · exact hnum.cexp.div Complex.differentiableAt_cos hcosnz
  constructor
  · intro z hz
    exact (hpoint z hz).1.differentiableWithinAt
  · intro z hz
    exact (hpoint z hz).2.differentiableWithinAt

end GaussianSourceAnalytic
#print axioms GaussianSourceAnalytic.eventually_differentiable_disk
