import GaussianParameterBranch
import GaussianSourceExponent
import ComplexKernelDiskLower

noncomputable section
namespace GaussianScalarFactor
open GaussianParameterBranch DiamondFreeKernelLimit

def gaussian (n : ℕ) (z : ℂ) : ℂ :=
  prefactor n z / finiteKernel n (parameter n z * Complex.I)

def errorConstant (r R : ℝ) : ℝ :=
  4*r^2/Real.cos R +
    2*(2*Real.exp R*R^2+4*Real.exp r*r^3)/(Real.cos R)^2

lemma cosine_difference (x z : ℂ) {r E : ℝ} (hz : ‖z‖≤r)
    (he : ‖x-z‖≤E) (hE : E≤1) :
    ‖Complex.cos x-Complex.cos z‖≤2*Real.exp r*E := by
  have hp := GaussianSourceExponent.exp_difference (x*Complex.I) (z*Complex.I)
    (by simpa using hz) (by simpa [← sub_mul] using he) hE
  have hm := GaussianSourceExponent.exp_difference (-(x*Complex.I)) (-(z*Complex.I))
    (by simpa using hz) (by
      rw [neg_sub_neg, ← sub_mul, norm_mul, Complex.norm_I, mul_one, norm_sub_rev]
      exact he) hE
  have hid : Complex.cos x-Complex.cos z =
      ((Complex.exp (x*Complex.I)-Complex.exp (z*Complex.I))+
        (Complex.exp (-(x*Complex.I))-Complex.exp (-(z*Complex.I))))/2 := by
    rw [← Complex.cosh_mul_I x, ← Complex.cosh_mul_I z]
    unfold Complex.cosh
    ring
  rw [hid,norm_div]
  norm_num only [Complex.norm_ofNat]
  have hh := norm_add_le (Complex.exp (x*Complex.I)-Complex.exp (z*Complex.I))
    (Complex.exp (-(x*Complex.I))-Complex.exp (-(z*Complex.I)))
  linarith

lemma quotient_error (p h c : ℂ) {P E d : ℝ}
    (hd : 0<d) (hh : d/2≤‖h‖) (hc : d≤‖c‖)
    (hp : ‖p-1‖≤P) (he : ‖h-c‖≤E) :
    ‖p/h-c⁻¹‖≤2*P/d+2*E/d^2 := by
  have hnz : h≠0 := norm_pos_iff.mp (by linarith)
  have cnz : c≠0 := norm_pos_iff.mp (hd.trans_le hc)
  have hih : ‖h⁻¹‖≤2/d := by
    rw [norm_inv]
    have hi := inv_anti₀ (show 0<d/2 by positivity) hh
    convert hi using 1 <;> field_simp
  have hic : ‖c⁻¹‖≤1/d := by
    simpa [norm_inv,one_div] using inv_anti₀ hd hc
  have hP : 0≤P := (norm_nonneg _).trans hp
  have hEn : 0≤E := (norm_nonneg _).trans he
  have hid : p/h-c⁻¹=(p-1)*h⁻¹+(c-h)*h⁻¹*c⁻¹ := by
    field_simp [hnz,cnz]
    <;> ring
  rw [hid]
  calc
    _ ≤ ‖(p-1)*h⁻¹‖+‖(c-h)*h⁻¹*c⁻¹‖ := norm_add_le _ _
    _ ≤ P*(2/d)+E*(2/d)*(1/d) := by
      simp only [norm_mul]
      apply add_le_add
      · exact mul_le_mul hp hih (norm_nonneg _) hP
      · apply mul_le_mul _ hic (norm_nonneg _) (by positivity)
        exact mul_le_mul (by simpa only [norm_sub_rev] using he) hih
          (norm_nonneg _) hEn
    _ = _ := by ring

/-- Explicit Gaussian scalar error. All assumptions are elementary order/radius
thresholds; no assumed kernel error, inverse estimate, or Gaussian limit occurs. -/
theorem gaussian_error (n : ℕ) (hn : 0<n) (z : ℂ) {r R : ℝ}
    (hr : 0≤r) (hrR : r<R) (hpi : R<Real.pi/2) (hz : ‖z‖≤r)
    (hbranch : r^2/(n:ℝ)^2≤1/2) (hscale : r^2/(n:ℝ)≤1)
    (hcontain : 2*r^3/(n:ℝ)^2≤R-r) (hmove : 2*r^3/(n:ℝ)^2≤1)
    (hsmall : R/(n:ℝ)≤1/2) (herr : R^2/(n:ℝ)≤1)
    (hthreshold : 2*Real.exp R*R^2/(n:ℝ)≤Real.cos R/2) :
    ‖gaussian n z-(Complex.cos z)⁻¹‖≤errorConstant r R/(n:ℝ) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  have hR : 0≤R := hr.trans hrR.le
  have hc : 0<Real.cos R := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos],hpi⟩
  have hkerr := parameter_error n z hz hbranch
  have hk : ‖parameter n z‖≤R := by
    have hh := norm_sub_norm_le (parameter n z) z
    linarith
  have hkernel := ComplexBinomialRate.finiteKernel_error n hn (parameter n z*Complex.I)
    R (by simpa using hk) hsmall herr
  simp only [Complex.cosh_mul_I] at hkernel
  have hcos := cosine_difference (parameter n z) z hz hkerr hmove
  have hdn : 2*r^3/(n:ℝ)^2≤2*r^3/(n:ℝ) := by
    apply div_le_div_of_nonneg_left (by positivity) hnR
    nlinarith
  have hmove1 : ‖Complex.cos (parameter n z)-Complex.cos z‖≤
      (4*Real.exp r*r^3)/(n:ℝ) := by
    calc
      _ ≤ 2*Real.exp r*(2*r^3/(n:ℝ)^2) := hcos
      _ ≤ 2*Real.exp r*(2*r^3/(n:ℝ)) := by gcongr
      _ = _ := by ring
  have he : ‖finiteKernel n (parameter n z*Complex.I)-Complex.cos z‖≤
      (2*Real.exp R*R^2+4*Real.exp r*r^3)/(n:ℝ) := by
    have hh := norm_sub_le_norm_sub_add_norm_sub (finiteKernel n (parameter n z*Complex.I))
      (Complex.cos (parameter n z)) (Complex.cos z)
    calc
      _ ≤ _ := hh
      _ ≤ 2*Real.exp R*R^2/(n:ℝ)+(4*Real.exp r*r^3)/(n:ℝ) := add_le_add hkernel hmove1
      _ = _ := by ring
  have hlow := ComplexKernelDiskLower.finite_kernel_lower n hn hR hpi hsmall herr hthreshold hk
  have hcoslow := ComplexKernelDiskLower.cosine_lower hR hpi (hz.trans hrR.le)
  have hh := quotient_error (prefactor n z) (finiteKernel n (parameter n z*Complex.I))
    (Complex.cos z) hc hlow hcoslow (prefactor_error n hn z hz hbranch hscale) he
  change ‖prefactor n z / finiteKernel n (parameter n z * Complex.I) - (Complex.cos z)⁻¹‖ ≤ _
  convert hh using 1 <;> simp only [errorConstant] <;> ring


lemma eventually_div_sq_le (A : ℝ) {B : ℝ} (hB : 0<B) :
    ∀ᶠ n : ℕ in Filter.atTop, A/(n:ℝ)^2≤B := by
  have hi : Filter.Tendsto (fun n : ℕ => (n:ℝ)⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hh : Filter.Tendsto (fun n : ℕ => A/(n:ℝ)^2) Filter.atTop (nhds 0) := by
    simpa [div_eq_mul_inv,inv_pow] using (tendsto_const_nhds.mul (hi.pow 2))
  filter_upwards [hh.eventually (gt_mem_nhds hB)] with n hn
  exact hn.le

/-- The order threshold is independent of the complex point in the closed
inner disk. This proves a quantitative locally uniform Gaussian scalar limit. -/
theorem eventually_uniform_gaussian_error {r R : ℝ}
    (hr : 0≤r) (hrR : r<R) (hpi : R<Real.pi/2) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ z : ℂ, ‖z‖≤r →
      ‖gaussian n z-(Complex.cos z)⁻¹‖≤errorConstant r R/(n:ℝ) := by
  have hs : Filter.Tendsto (fun n : ℕ => r^2/(n:ℝ)) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  filter_upwards [ComplexKernelDiskLower.eventually_thresholds (hr.trans hrR.le) hpi,
    eventually_div_sq_le (r^2) (by norm_num : (0:ℝ)<1/2),
    hs.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num)),
    eventually_div_sq_le (2*r^3) (sub_pos.mpr hrR),
    eventually_div_sq_le (2*r^3) (show (0:ℝ)<1 by norm_num)]
      with n hn hb hscale hcontain hmove
  intro z hz
  exact gaussian_error n hn.1 z hr hrR hpi hz hb hscale.le hcontain hmove
    hn.2.1 hn.2.2.1 hn.2.2.2

@[simp] theorem gaussian_zero (n : ℕ) : gaussian n 0=1 := by
  simp [gaussian,finiteKernel]

end GaussianScalarFactor
#print axioms GaussianScalarFactor.gaussian_error

#print axioms GaussianScalarFactor.eventually_uniform_gaussian_error
