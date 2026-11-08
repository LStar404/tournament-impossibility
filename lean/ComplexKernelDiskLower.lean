import ComplexBinomialRate

noncomputable section
namespace ComplexKernelDiskLower
open Complex

/-- A concrete cosine lower bound on a disk strictly inside pi/2. -/
theorem cosine_lower {R : ℝ} (hR : 0≤R) (hpi : R<Real.pi/2)
    {w : ℂ} (hw : ‖w‖≤R) : Real.cos R ≤ ‖Complex.cos w‖ := by
  have habs : |w.re|≤R := (Complex.abs_re_le_norm w).trans hw
  have hcos : Real.cos R ≤ Real.cos w.re := by
    simpa only [Real.cos_abs] using Real.cos_le_cos_of_nonneg_of_le_pi
      (abs_nonneg w.re) (show R≤Real.pi by linarith [Real.pi_pos]) habs
  have hp : 0<Real.cos R := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],hpi⟩
  have hre : (Complex.cos w).re = Real.cos w.re * Real.cosh w.im := by
    conv_lhs => rw [← Complex.re_add_im w, Complex.cos_add]
    simp [Complex.cos_mul_I,Complex.sin_mul_I,Complex.cos_ofReal_re]
  calc
    Real.cos R ≤ Real.cos w.re * Real.cosh w.im := by
      have h := Real.one_le_cosh w.im
      nlinarith
    _ = (Complex.cos w).re := hre.symm
    _ ≤ |(Complex.cos w).re| := le_abs_self _
    _ ≤ ‖Complex.cos w‖ := Complex.abs_re_le_norm _

/-- An explicit finite-order denominator lower bound, uniform over the disk.
The last hypothesis is a concrete threshold in n, not an assumed zero-free
property of the graph kernel. -/
theorem finite_kernel_lower (n : ℕ) (hn : 0<n) {R : ℝ}
    (hR : 0≤R) (hpi : R<Real.pi/2) (hsmall : R/(n:ℝ)≤1/2)
    (herr : R^2/(n:ℝ)≤1) (hthreshold : 2*Real.exp R*R^2/(n:ℝ)≤Real.cos R/2)
    {w : ℂ} (hw : ‖w‖≤R) :
    Real.cos R/2 ≤ ‖DiamondFreeKernelLimit.finiteKernel n (w*Complex.I)‖ := by
  have he := ComplexBinomialRate.finiteKernel_error n hn (w*Complex.I) R
    (by simpa using hw) hsmall herr
  simp only [Complex.cosh_mul_I] at he
  have hc := cosine_lower hR hpi hw
  have ht := norm_sub_norm_le (Complex.cos w)
    (DiamondFreeKernelLimit.finiteKernel n (w*Complex.I))
  rw [norm_sub_rev] at ht
  linarith
theorem eventually_thresholds {R : ℝ} (hR : 0≤R) (hpi : R<Real.pi/2) :
    ∀ᶠ n : ℕ in Filter.atTop, 0<n ∧ R/(n:ℝ)≤1/2 ∧ R^2/(n:ℝ)≤1 ∧
      2*Real.exp R*R^2/(n:ℝ)≤Real.cos R/2 := by
  have hp : 0<Real.cos R/2 := by
    have h := Real.cos_pos_of_mem_Ioo (x := R) ⟨by linarith [Real.pi_pos],hpi⟩
    positivity
  have h1 : Filter.Tendsto (fun n : ℕ => R/(n:ℝ)) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h2 : Filter.Tendsto (fun n : ℕ => R^2/(n:ℝ)) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h3 : Filter.Tendsto (fun n : ℕ => 2*Real.exp R*R^2/(n:ℝ)) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  filter_upwards [Filter.eventually_gt_atTop (0:ℕ),
    h1.eventually (gt_mem_nhds (show (0:ℝ)<1/2 by norm_num)),
    h2.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num)),
    h3.eventually (gt_mem_nhds hp)] with n hn ha hb hc
  exact ⟨hn,ha.le,hb.le,hc.le⟩

end ComplexKernelDiskLower
#print axioms ComplexKernelDiskLower.finite_kernel_lower

#print axioms ComplexKernelDiskLower.eventually_thresholds
