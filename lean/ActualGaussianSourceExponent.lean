import GaussianSourceExponent
import GaussianParameterBranch
import ActualComplexScoreSource

noncomputable section
open Filter Topology DiamondGap
namespace ActualGaussianSourceExponent
open GaussianParameterBranch ActualComplexScoreSource DiamondFreeDiskResolvent

def sourceConstant (R K : ℝ) : ℝ := K*(diskConstant R)^2
def errorConstant (r R K : ℝ) : ℝ :=
  4*Real.exp r*(r^2+R^2*sourceConstant R K)

def actualExponent {n : ℕ} (T : Tournament (Fin n)) (v z : ℂ) : ℂ :=
  GaussianSourceExponent.exponent n (v*z) (parameter n z) (source T (parameter n z))

lemma parameter_in_disk (n : ℕ) (z : ℂ) {r R : ℝ} (hz : ‖z‖≤r)
    (hbranch : r^2/(n:ℝ)^2≤1/2) (hgap : 2*r^3/(n:ℝ)^2≤R-r) :
    ‖parameter n z‖≤R := by
  have he := GaussianParameterBranch.parameter_error n z hz hbranch
  have ht := norm_add_le (parameter n z-z) z
  rw [sub_add_cancel] at ht
  linarith

/-- Finite-order assembly retaining only explicitly listed scalar thresholds
and the actual normalized source conclusion at the substituted parameter. -/
theorem finite_error {n : ℕ} (hn : 0<n) (T : Tournament (Fin n)) (v z : ℂ)
    {r R K : ℝ} (hK : 0≤K) (hv : ‖v‖≤1) (hz : ‖z‖≤r)
    (hsmall : r/(n:ℝ)≤1/2) (hbranch : r^2/(n:ℝ)^2≤1/2)
    (hgap : 2*r^3/(n:ℝ)^2≤R-r)
    (hscale : 2*(r^2+R^2*sourceConstant R K)/(n:ℝ)≤1)
    (hsource : ‖source T (parameter n z)‖/(n:ℝ)^2≤ sourceConstant R K/(n:ℝ)) :
    ‖Complex.exp (actualExponent T v z)-Complex.exp (v*z)‖≤errorConstant r R K/(n:ℝ) := by
  have ha : ‖v*z‖≤r := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right hv (norm_nonneg z)).trans (by simpa using hz)
  have hk := parameter_in_disk n z hz hbranch hgap
  have hB : 0≤ sourceConstant R K := mul_nonneg hK (sq_nonneg _)
  exact GaussianSourceExponent.exp_exponent_error n hn (v*z) (parameter n z)
    (source T (parameter n z)) ha hsmall hk hB hsource hscale

lemma eventually_div_le (C ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, C/(n:ℝ)≤ε := by
  have h : Tendsto (fun n : ℕ => C/(n:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  filter_upwards [h.eventually (gt_mem_nhds hε)] with n hn
  exact hn.le

lemma eventually_div_sq_le (C ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, C/(n:ℝ)^2≤ε := by
  have hi : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h : Tendsto (fun n : ℕ => C/(n:ℝ)^2) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv,inv_pow] using tendsto_const_nhds.mul (hi.pow 2)
  filter_upwards [h.eventually (gt_mem_nhds hε)] with n hn
  exact hn.le

/-- The graph-independent order threshold is uniform in the whole inner disk,
all actual zero-diamond graphs, and every |v|<=1. The source estimate is proved
for the actual substituted S1 resolvent, not assumed as an external premise. -/
theorem eventually_uniform_error {r R K : ℝ} (hr : 0≤r) (hrR : r<R)
    (hRpi : R<Real.pi/2) (hK : 0≤K) :
    ∀ᶠ n : ℕ in atTop, ∀ (T : Tournament (Fin n)), T.diamonds.card=0 →
      scoreEnergy T≤K*(n:ℝ) → ∀ (z v : ℂ), ‖z‖≤r → ‖v‖≤1 →
        ‖Complex.exp (actualExponent T v z)-Complex.exp (v*z)‖≤errorConstant r R K/(n:ℝ) := by
  have hR : 0≤R := hr.trans hrR.le
  filter_upwards [eventually_gt_atTop (0:ℕ),
    ActualComplexScoreSource.eventually_uniform_actual_source hR hRpi,
    eventually_div_le r (1/2) (by norm_num),
    eventually_div_sq_le (r^2) (1/2) (by norm_num),
    eventually_div_sq_le (2*r^3) (R-r) (sub_pos.mpr hrR),
    eventually_div_le (2*(r^2+R^2*sourceConstant R K)) 1 (by norm_num)]
      with n hn hsource hsmall hbranch hgap hscale
  intro T hT henergy z v hz hv
  have hk := parameter_in_disk n z hz hbranch hgap
  have hs := hsource T hT (parameter n z) hk K henergy
  exact finite_error hn T v z hK hv hz hsmall hbranch hgap hscale hs

/-- Explicit O(1/n) constant for the actual exponential source factor. -/
theorem exists_uniform_constant {r R K : ℝ} (hr : 0≤r) (hrR : r<R)
    (hRpi : R<Real.pi/2) (hK : 0≤K) :
    ∃ C : ℝ, 0≤C ∧ C=errorConstant r R K ∧
      ∀ᶠ n : ℕ in atTop, ∀ (T : Tournament (Fin n)), T.diamonds.card=0 →
        scoreEnergy T≤K*(n:ℝ) → ∀ (z v : ℂ), ‖z‖≤r → ‖v‖≤1 →
          ‖Complex.exp (actualExponent T v z)-Complex.exp (v*z)‖≤C/(n:ℝ) := by
  refine ⟨errorConstant r R K,?_,rfl,eventually_uniform_error hr hrR hRpi hK⟩
  unfold errorConstant sourceConstant
  positivity

end ActualGaussianSourceExponent
#print axioms ActualGaussianSourceExponent.eventually_uniform_error
#print axioms ActualGaussianSourceExponent.exists_uniform_constant
