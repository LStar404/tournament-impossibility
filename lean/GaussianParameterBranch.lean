import ComplexBinomialRate
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

noncomputable section
namespace GaussianParameterBranch

def beta (n : ℕ) (z : ℂ) : ℂ := 1-(z/(n:ℂ))^2
def logBeta (n : ℕ) (z : ℂ) : ℂ := Complex.log (beta n z)
def root (n : ℕ) (z : ℂ) : ℂ := Complex.exp (-logBeta n z/2)
def parameter (n : ℕ) (z : ℂ) : ℂ := z*root n z
def prefactor (n : ℕ) (z : ℂ) : ℂ := Complex.exp (-(n:ℂ)*logBeta n z/2)

lemma ratio_square_bound (n : ℕ) (z : ℂ) {R : ℝ} (hz : ‖z‖≤R) :
    ‖(z/(n:ℂ))^2‖ ≤ R^2/(n:ℝ)^2 := by
  have hR : 0≤R := (norm_nonneg _).trans hz
  simp only [norm_pow, norm_div, Complex.norm_natCast, div_pow]
  exact div_le_div_of_nonneg_right ((sq_le_sq₀ (norm_nonneg _) hR).mpr hz) (sq_nonneg _)

lemma beta_slitPlane (n : ℕ) (z : ℂ) {R : ℝ} (hz : ‖z‖≤R)
    (hsmall : R^2/(n:ℝ)^2≤1/2) : beta n z ∈ Complex.slitPlane := by
  have hu : ‖-((z/(n:ℂ))^2)‖<1 := by
    rw [norm_neg]
    exact (ratio_square_bound n z hz).trans hsmall |>.trans_lt (by norm_num)
  simpa [beta,sub_eq_add_neg] using Complex.mem_slitPlane_of_norm_lt_one hu

lemma beta_ne_zero (n : ℕ) (z : ℂ) {R : ℝ} (hz : ‖z‖≤R)
    (hsmall : R^2/(n:ℝ)^2≤1/2) : beta n z ≠ 0 :=
  Complex.slitPlane_ne_zero (beta_slitPlane n z hz hsmall)

lemma logBeta_bound (n : ℕ) (z : ℂ) {R : ℝ} (hz : ‖z‖≤R)
    (hsmall : R^2/(n:ℝ)^2≤1/2) : ‖logBeta n z‖ ≤ 2*R^2/(n:ℝ)^2 := by
  have hu : ‖-((z/(n:ℂ))^2)‖≤1/2 := by
    simpa using (ratio_square_bound n z hz).trans hsmall
  have hh := Complex.norm_log_one_add_half_le_self hu
  have hb := ratio_square_bound n z hz
  simp only [norm_neg] at hh
  change ‖Complex.log (1-(z/(n:ℂ))^2)‖≤_
  rw [sub_eq_add_neg]
  calc
    _ ≤ 2*‖(z/(n:ℂ))^2‖ := by nlinarith [norm_nonneg ((z/(n:ℂ))^2)]
    _ ≤ 2*(R^2/(n:ℝ)^2) := mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = _ := by ring

lemma root_identity (n : ℕ) (z : ℂ) (hb : beta n z ≠ 0) :
    (root n z)^2*beta n z=1 := by
  rw [root, ← Complex.exp_nat_mul, ← Complex.exp_log hb, ← Complex.exp_add]
  have he : (2:ℂ)*(-logBeta n z/2)+Complex.log (beta n z)=0 := by
    unfold logBeta
    ring
  norm_num only [Nat.cast_ofNat]
  rw [he, Complex.exp_zero]

@[simp] lemma root_zero (n : ℕ) : root n 0=1 := by simp [root,logBeta,beta]
@[simp] lemma parameter_zero (n : ℕ) : parameter n 0=0 := by simp [parameter]
@[simp] lemma prefactor_zero (n : ℕ) : prefactor n 0=1 := by simp [prefactor,logBeta,beta]

lemma root_error (n : ℕ) (z : ℂ) {R : ℝ} (hz : ‖z‖≤R)
    (hsmall : R^2/(n:ℝ)^2≤1/2) :
    ‖root n z-1‖≤2*R^2/(n:ℝ)^2 := by
  have hl := logBeta_bound n z hz hsmall
  have he : ‖-logBeta n z/2‖≤R^2/(n:ℝ)^2 := by
    simp only [norm_div,norm_neg,Complex.norm_ofNat]
    calc
      _ ≤ (2*R^2/(n:ℝ)^2)/2 := div_le_div_of_nonneg_right hl (by norm_num)
      _ = _ := by ring
  have hs : ‖-logBeta n z/2‖≤1 := he.trans (hsmall.trans (by norm_num))
  apply (Complex.norm_exp_sub_one_le hs).trans
  convert mul_le_mul_of_nonneg_left he (by norm_num : (0:ℝ)≤2) using 1; ring

theorem parameter_error (n : ℕ) (z : ℂ) {R : ℝ} (hz : ‖z‖≤R)
    (hsmall : R^2/(n:ℝ)^2≤1/2) :
    ‖parameter n z-z‖≤2*R^3/(n:ℝ)^2 := by
  have hR : 0≤R := (norm_nonneg _).trans hz
  have he : parameter n z-z=z*(root n z-1) := by unfold parameter; ring
  rw [he,norm_mul]
  calc
    _ ≤ R*(2*R^2/(n:ℝ)^2) := mul_le_mul hz (root_error n z hz hsmall)
      (norm_nonneg _) hR
    _ = _ := by ring

theorem prefactor_error (n : ℕ) (hn : 0<n) (z : ℂ) {R : ℝ} (hz : ‖z‖≤R)
    (hsmall : R^2/(n:ℝ)^2≤1/2) (hscale : R^2/(n:ℝ)≤1) :
    ‖prefactor n z-1‖≤2*R^2/(n:ℝ) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hl := logBeta_bound n z hz hsmall
  have he : ‖-(n:ℂ)*logBeta n z/2‖≤R^2/(n:ℝ) := by
    simp only [norm_div,norm_mul,norm_neg,Complex.norm_natCast,Complex.norm_ofNat]
    calc
      _ ≤ (n:ℝ)*(2*R^2/(n:ℝ)^2)/2 := by gcongr
      _ = _ := by field_simp
  apply (Complex.norm_exp_sub_one_le (he.trans hscale)).trans
  convert mul_le_mul_of_nonneg_left he (by norm_num : (0:ℝ)≤2) using 1; ring

lemma differentiableAt_beta (n : ℕ) (z : ℂ) : DifferentiableAt ℂ (beta n) z := by
  unfold beta
  fun_prop

lemma differentiableAt_logBeta (n : ℕ) (z : ℂ) {R : ℝ} (hz : ‖z‖≤R)
    (hsmall : R^2/(n:ℝ)^2≤1/2) : DifferentiableAt ℂ (logBeta n) z :=
  (differentiableAt_beta n z).clog (beta_slitPlane n z hz hsmall)

theorem differentiableOn_parameter (n : ℕ) {R : ℝ}
    (hsmall : R^2/(n:ℝ)^2≤1/2) :
    DifferentiableOn ℂ (parameter n) {z | ‖z‖≤R} := by
  intro z hz
  have hlog := differentiableAt_logBeta n z hz hsmall
  have hroot : DifferentiableAt ℂ (root n) z := by
    unfold root
    exact (hlog.neg.div_const 2).cexp
  exact (differentiableAt_id.mul hroot).differentiableWithinAt

theorem differentiableOn_prefactor (n : ℕ) {R : ℝ}
    (hsmall : R^2/(n:ℝ)^2≤1/2) :
    DifferentiableOn ℂ (prefactor n) {z | ‖z‖≤R} := by
  intro z hz
  have hlog := differentiableAt_logBeta n z hz hsmall
  exact (((hlog.const_mul (-(n:ℂ))).div_const 2).cexp).differentiableWithinAt

end GaussianParameterBranch
#print axioms GaussianParameterBranch.root_identity
#print axioms GaussianParameterBranch.parameter_error
#print axioms GaussianParameterBranch.prefactor_error
#print axioms GaussianParameterBranch.differentiableOn_parameter

#print axioms GaussianParameterBranch.differentiableOn_prefactor
