import GaussianScalarFactor
import ActualGaussianSourceExponent

noncomputable section
open Filter Topology DiamondGap
namespace GaussianSourceProduct

/-- The actual Gaussian/source product, using the proved principal-log branch
and the actual tournament S1 resolvent source. -/
def product {n : ℕ} (T : Tournament (Fin n)) (v z : ℂ) : ℂ :=
  GaussianScalarFactor.gaussian n z * Complex.exp (ActualGaussianSourceExponent.actualExponent T v z)

def target (v z : ℂ) : ℂ := Complex.exp (v*z)/Complex.cos z

def errorConstant (r R K : ℝ) : ℝ :=
  (1/Real.cos R+GaussianScalarFactor.errorConstant r R)*
    ActualGaussianSourceExponent.errorConstant r R K +
  Real.exp r*GaussianScalarFactor.errorConstant r R

/-- Pure scalar error assembly; the actual theorem below discharges both
factor-error premises from the previously verified graph-level estimates. -/
lemma scalar_product_error (n : ℕ) (hn : 0 < n) (g s z v : ℂ)
    {r R Cg Cs : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hpi : R < Real.pi/2)
    (hz : ‖z‖ ≤ r) (hv : ‖v‖ ≤ 1) (hCg : 0 ≤ Cg) (hCs : 0 ≤ Cs)
    (hg : ‖g-(Complex.cos z)⁻¹‖ ≤ Cg/(n : ℝ))
    (hs : ‖s-Complex.exp (v*z)‖ ≤ Cs/(n : ℝ)) :
    ‖g*s-Complex.exp (v*z)/Complex.cos z‖ ≤
      ((1/Real.cos R+Cg)*Cs+Real.exp r*Cg)/(n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hR : 0 ≤ R := hr.trans hrR.le
  have hc : 0 < Real.cos R := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos],hpi⟩
  have hcos := ComplexKernelDiskLower.cosine_lower hR hpi (hz.trans hrR.le)
  have hsec : ‖(Complex.cos z)⁻¹‖ ≤ 1/Real.cos R := by
    rw [norm_inv, one_div]
    exact inv_anti₀ hc hcos
  have hCgdiv : Cg/(n : ℝ) ≤ Cg := by
    apply (div_le_iff₀ hnR).mpr
    nlinarith
  have hgnorm : ‖g‖ ≤ 1/Real.cos R+Cg := by
    have hh := norm_le_norm_sub_add g ((Complex.cos z)⁻¹)
    linarith
  have hvz : ‖v*z‖ ≤ r := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right hv (norm_nonneg z)).trans (by simpa using hz)
  have hexp : ‖Complex.exp (v*z)‖ ≤ Real.exp r :=
    (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr hvz)
  have hid : g*s-Complex.exp (v*z)/Complex.cos z =
      g*(s-Complex.exp (v*z))+Complex.exp (v*z)*(g-(Complex.cos z)⁻¹) := by
    simp only [div_eq_mul_inv]
    ring
  rw [hid]
  calc
    _ ≤ ‖g*(s-Complex.exp (v*z))‖ +
        ‖Complex.exp (v*z)*(g-(Complex.cos z)⁻¹)‖ := norm_add_le _ _
    _ ≤ (1/Real.cos R+Cg)*(Cs/(n : ℝ))+Real.exp r*(Cg/(n : ℝ)) := by
      simp only [norm_mul]
      apply add_le_add
      · exact mul_le_mul hgnorm hs (norm_nonneg _) (by positivity)
      · exact mul_le_mul hexp hg (norm_nonneg _) (Real.exp_pos r).le
    _ = _ := by ring

/-- One order threshold works for every actual zero-diamond tournament of
linear score energy, every point in the closed inner disk and every |v|<=1.
No Gaussian/source error is assumed as an external premise. -/
theorem eventually_uniform_error {r R K : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (hpi : R < Real.pi/2) (hK : 0 ≤ K) :
    ∀ᶠ n : ℕ in atTop, ∀ (T : Tournament (Fin n)), T.diamonds.card=0 →
      ActualComplexScoreSource.scoreEnergy T ≤ K*(n : ℝ) → ∀ (z v : ℂ),
      ‖z‖ ≤ r → ‖v‖ ≤ 1 →
      ‖product T v z-target v z‖ ≤ errorConstant r R K/(n : ℝ) := by
  have hR : 0 ≤ R := hr.trans hrR.le
  have hc : 0 < Real.cos R := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos],hpi⟩
  have hCg : 0 ≤ GaussianScalarFactor.errorConstant r R := by
    unfold GaussianScalarFactor.errorConstant
    positivity
  have hCs : 0 ≤ ActualGaussianSourceExponent.errorConstant r R K := by
    unfold ActualGaussianSourceExponent.errorConstant ActualGaussianSourceExponent.sourceConstant
    positivity
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    GaussianScalarFactor.eventually_uniform_gaussian_error hr hrR hpi,
    ActualGaussianSourceExponent.eventually_uniform_error hr hrR hpi hK]
    with n hn hg hs
  intro T hT henergy z v hz hv
  exact scalar_product_error n hn _ _ z v hr hrR hpi hz hv hCg hCs
    (hg z hz) (hs T hT henergy z v hz hv)

/-- Explicit nonnegative constant for the actual product estimate. -/
theorem exists_uniform_constant {r R K : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (hpi : R < Real.pi/2) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ C=errorConstant r R K ∧
      ∀ᶠ n : ℕ in atTop, ∀ (T : Tournament (Fin n)), T.diamonds.card=0 →
        ActualComplexScoreSource.scoreEnergy T ≤ K*(n : ℝ) → ∀ (z v : ℂ),
        ‖z‖ ≤ r → ‖v‖ ≤ 1 →
        ‖product T v z-target v z‖ ≤ C/(n : ℝ) := by
  refine ⟨errorConstant r R K,?_,rfl,eventually_uniform_error hr hrR hpi hK⟩
  have hR : 0 ≤ R := hr.trans hrR.le
  have hc : 0 < Real.cos R := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos],hpi⟩
  unfold errorConstant GaussianScalarFactor.errorConstant
    ActualGaussianSourceExponent.errorConstant ActualGaussianSourceExponent.sourceConstant
  positivity

end GaussianSourceProduct
#print axioms GaussianSourceProduct.eventually_uniform_error
#print axioms GaussianSourceProduct.exists_uniform_constant
