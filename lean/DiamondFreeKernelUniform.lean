import DiamondFreeKernelLimit
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

noncomputable section
open Filter Topology Asymptotics
namespace DiamondFreeKernelUniform
open DiamondFreeKernelLimit

/-- A filter-general binomial limit, allowing order and parameter to vary independently. -/
theorem binomial_filter {α : Type*} {l : Filter α} {n : α → ℕ} {w : α → ℂ}
    {z : ℂ} (hn : Tendsto n l atTop) (hw : Tendsto w l (𝓝 z)) :
    Tendsto (fun a => (1 + w a / (n a : ℂ))^(n a)) l (𝓝 (Complex.exp z)) := by
  have hi : Tendsto (fun a => (n a : ℂ)⁻¹) l (𝓝 0) := by
    simpa only [Function.comp_def, Complex.ofReal_inv, Complex.ofReal_natCast, Complex.ofReal_zero] using
      (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hn)).ofReal
  have hg : Tendsto (fun a => w a / (n a : ℂ)) l (𝓝 0) := by
    simpa [div_eq_mul_inv] using hw.mul hi
  have hnon : ∀ᶠ a in l, (n a : ℂ) ≠ 0 := by
    filter_upwards [hn.eventually (eventually_gt_atTop (0 : ℕ))] with a ha
    exact_mod_cast Nat.ne_of_gt ha
  have hmain : Tendsto (fun a => (n a : ℂ) * (w a / (n a : ℂ))) l (𝓝 z) := by
    apply hw.congr'
    filter_upwards [hnon] with a ha
    field_simp
  have he : (fun a => (n a : ℂ) * (Complex.log (1 + w a / (n a : ℂ)) - w a / (n a : ℂ)))
      =O[l] (fun a => w a ^ 2 * (n a : ℂ)⁻¹) := by
    have h := (isBigO_refl (fun a => (n a : ℂ)) l).mul
      (Complex.log_sub_self_isBigO.comp_tendsto hg)
    apply h.congr' Filter.EventuallyEq.rfl
    filter_upwards [hnon] with a ha
    dsimp
    field_simp
  have herr := he.trans_tendsto (by simpa using (hw.pow 2).mul hi)
  have hlog : Tendsto (fun a => (n a : ℂ) * Complex.log (1 + w a / (n a : ℂ))) l (𝓝 z) := by
    convert hmain.add herr using 1
    · ext a
      ring
    · simp
  apply (Complex.continuous_exp.continuousAt.tendsto.comp hlog).congr'
  filter_upwards [hg.eventually_ne (show (0 : ℂ) ≠ -1 by norm_num)] with a ha
  dsimp only [Function.comp_def]
  rw [Complex.exp_nat_mul, Complex.exp_log]
  intro hh
  apply ha
  linear_combination hh

theorem kernel_filter {α : Type*} {l : Filter α} {n : α → ℕ} {w : α → ℂ}
    {z : ℂ} (hn : Tendsto n l atTop) (hw : Tendsto w l (𝓝 z)) :
    Tendsto (fun a => finiteKernel (n a) (w a)) l (𝓝 (Complex.cosh z)) := by
  simpa [finiteKernel, Complex.cosh, neg_div, sub_eq_add_neg] using
    ((binomial_filter hn hw).add (binomial_filter hn hw.neg)).div_const (2 : ℂ)

/-- Qualitative locally uniform convergence; no convergence rate is claimed. -/
theorem locallyUniform : TendstoLocallyUniformly finiteKernel Complex.cosh atTop := by
  apply tendstoLocallyUniformly_iff_forall_tendsto.mpr
  intro z
  apply tendsto_uniformity_iff_dist_tendsto_zero.mpr
  have hf : Tendsto (fun p : ℕ × ℂ => finiteKernel p.1 p.2)
      (atTop ×ˢ 𝓝 z) (𝓝 (Complex.cosh z)) := kernel_filter tendsto_fst tendsto_snd
  have hh : Tendsto (fun p : ℕ × ℂ => Complex.cosh p.2)
      (atTop ×ˢ 𝓝 z) (𝓝 (Complex.cosh z)) :=
    Complex.continuous_cosh.continuousAt.tendsto.comp tendsto_snd
  simpa using hh.dist hf

theorem uniformlyOn_compact {K : Set ℂ} (hK : IsCompact K) :
    TendstoUniformlyOn finiteKernel Complex.cosh atTop K :=
  tendstoLocallyUniformly_iff_forall_isCompact.mp locallyUniform K hK

/-- The imaginary parameter has the cosine limit, uniformly on compact sets. -/
theorem imaginary_locallyUniform :
    TendstoLocallyUniformly (fun n w => finiteKernel n (w * Complex.I)) Complex.cos atTop := by
  apply tendstoLocallyUniformly_iff_forall_tendsto.mpr
  intro z
  apply tendsto_uniformity_iff_dist_tendsto_zero.mpr
  have hf : Tendsto (fun p : ℕ × ℂ => finiteKernel p.1 (p.2 * Complex.I))
      (atTop ×ˢ 𝓝 z) (𝓝 (Complex.cos z)) := by
    simpa only [Complex.cosh_mul_I] using
      kernel_filter (n := fun p : ℕ × ℂ => p.1) tendsto_fst
        (tendsto_snd.mul_const Complex.I)
  have hh : Tendsto (fun p : ℕ × ℂ => Complex.cos p.2)
      (atTop ×ˢ 𝓝 z) (𝓝 (Complex.cos z)) :=
    Complex.continuous_cos.continuousAt.tendsto.comp tendsto_snd
  simpa using hh.dist hf

theorem imaginary_uniformlyOn_compact {K : Set ℂ} (hK : IsCompact K) :
    TendstoUniformlyOn (fun n w => finiteKernel n (w * Complex.I)) Complex.cos atTop K :=
  tendstoLocallyUniformly_iff_forall_isCompact.mp imaginary_locallyUniform K hK

/-- Reciprocal scalar kernels, not matrix operator inverses, converge uniformly
on compact subsets on which the limiting cosine does not vanish. No rate is claimed. -/
theorem inverse_uniformlyOn_compact {K : Set ℂ} (hK : IsCompact K)
    (hz : ∀ z ∈ K, Complex.cos z ≠ 0) :
    TendstoUniformlyOn (fun n w => (finiteKernel n (w * Complex.I))⁻¹)
      (fun w => (Complex.cos w)⁻¹) atTop K := by
  apply (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
  apply tendstoLocallyUniformlyOn_iff_forall_tendsto.mpr
  intro z hzk
  apply tendsto_uniformity_iff_dist_tendsto_zero.mpr
  have hw : Tendsto (fun p : ℕ × ℂ => p.2) (atTop ×ˢ 𝓝[K] z) (𝓝 z) :=
    tendsto_snd.mono_right nhdsWithin_le_nhds
  have hf : Tendsto (fun p : ℕ × ℂ => finiteKernel p.1 (p.2 * Complex.I))
      (atTop ×ˢ 𝓝[K] z) (𝓝 (Complex.cos z)) := by
    simpa only [Complex.cosh_mul_I] using
      kernel_filter (n := fun p : ℕ × ℂ => p.1) tendsto_fst
        (hw.mul_const Complex.I)
  have hh := Complex.continuous_cos.continuousAt.tendsto.comp hw
  simpa using (hh.inv₀ (hz z hzk)).dist (hf.inv₀ (hz z hzk))

/-- Compact-uniform convergence for actual zero-diamond graph families. -/
theorem actual_imaginary_uniformlyOn_compact
    (T : (n : ℕ) → DiamondGap.Tournament (Fin n))
    (hT : ∀ n, (T n).diamonds.card = 0) {K : Set ℂ} (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun n w => (DiamondFreeKernelDeterminant.kernel (T n) (w * Complex.I / (n : ℂ))).det)
      Complex.cos atTop K := by
  have he : (fun n w => (DiamondFreeKernelDeterminant.kernel (T n) (w * Complex.I / (n : ℂ))).det) =
      (fun n w => finiteKernel n (w * Complex.I)) := by
    funext n w
    simpa [finiteKernel] using
      DiamondFreeKernelDeterminant.zero_diamonds_kernel_det (T n) (hT n) (w * Complex.I / (n : ℂ))
  rw [he]
  exact imaginary_uniformlyOn_compact hK

end DiamondFreeKernelUniform
#print axioms DiamondFreeKernelUniform.uniformlyOn_compact
#print axioms DiamondFreeKernelUniform.inverse_uniformlyOn_compact

#print axioms DiamondFreeKernelUniform.actual_imaginary_uniformlyOn_compact
