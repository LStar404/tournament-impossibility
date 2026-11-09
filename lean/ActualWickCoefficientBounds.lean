import ActualWickUniformDisk
import WickCoefficientCauchy

noncomputable section
namespace ActualWickCoefficientBounds
open Filter Topology ActualWickUniformDisk

def bound (s R K : ℝ) := Real.exp s/Real.cos R+GaussianSourceProduct.errorConstant s R K

theorem target_bound {s R : ℝ} (hs : 0 ≤ s) (hsR : s < R) (hR : R < Real.pi/2)
    (v z : ℂ) (hv : ‖v‖ ≤ 1) (hz : ‖z‖ ≤ s) :
    ‖GaussianSourceProduct.target v z‖ ≤ Real.exp s/Real.cos R := by
  have hc : 0 < Real.cos R := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],hR⟩
  have hcos := ComplexKernelDiskLower.cosine_lower (hs.trans hsR.le) hR (hz.trans hsR.le)
  have hnum : ‖Complex.exp (v*z)‖ ≤ Real.exp s := by
    apply (Complex.norm_exp_le_exp_norm _).trans
    apply Real.exp_le_exp.mpr
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right hv (norm_nonneg z)).trans (by simpa using hz)
  rw [GaussianSourceProduct.target,norm_div]
  exact div_le_div₀ (Real.exp_pos s).le hnum hc hcos

theorem eventually_coefficients {s R K : ℝ} (hs : 0 < s) (hsR : s < R)
    (hR : R < Real.pi/2) (hK : 0 ≤ K) :
    0 ≤ bound s R K ∧ ∀ᶠ n : ℕ in atTop,
      ∀ T : DiamondGap.Tournament (Fin n), T.diamonds.card=0 →
        ActualComplexScoreSource.scoreEnergy T ≤ K*(n:ℝ) → ∀ v : ℂ, v^2=1 →
          ∀ k, ‖coefficient T v k‖ ≤ bound s R K/s^k := by
  obtain ⟨C,hC,hCe,herr⟩ := GaussianSourceProduct.exists_uniform_constant hs.le hsR hR hK
  subst C
  have hc : 0 < Real.cos R := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],hR⟩
  constructor
  · unfold bound; positivity
  · let t := (s+R)/2
    have ht : 0 ≤ t := by dsimp [t]; linarith
    have hst : s < t := by dsimp [t]; linarith
    have htR : t < R := by dsimp [t]; linarith
    filter_upwards [herr,GaussianSourceAnalytic.eventually_differentiable_disk ht htR hR,
      eventually_ge_atTop 1] with n he hd hn
    intro T hT hE v hv k
    have hn' : 0 < n := by omega
    have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
    have hdiff := (hd T hT v (norm_branch v hv)).1
    have hsub : Metric.closedBall (0:ℂ) s ⊆ Metric.ball 0 t := Metric.closedBall_subset_ball hst
    apply WickCoefficientCauchy.coefficient_bound (coefficient_germ hn' T hT v hv) hs
      (hdiff.diffContOnCl_ball hsub)
    intro z hz
    have hz' : ‖z‖ ≤ s := by simpa using (Metric.sphere_subset_closedBall hz)
    have he' := he T hT hE z v hz' (norm_branch v hv)
    have htar := target_bound hs.le hsR hR v z (norm_branch v hv) hz'
    have hnC : GaussianSourceProduct.errorConstant s R K/(n:ℝ) ≤ GaussianSourceProduct.errorConstant s R K :=
      div_le_self hC hnR
    have htri := norm_le_norm_sub_add (GaussianSourceProduct.product T v z) (GaussianSourceProduct.target v z)
    unfold bound
    linarith

theorem eventually_weighted {ρ s R K : ℝ} (hρ : 0 ≤ ρ) (hρs : ρ < s)
    (hsR : s < R) (hR : R < Real.pi/2) (hK : 0 ≤ K) :
    ∀ᶠ n : ℕ in atTop, ∀ T : DiamondGap.Tournament (Fin n), T.diamonds.card=0 →
      ActualComplexScoreSource.scoreEnergy T ≤ K*(n:ℝ) → ∀ v : ℂ, v^2=1 →
      Summable (fun k => ‖coefficient T v k‖*ρ^k) ∧
      (∑'k, ‖coefficient T v k‖*ρ^k) ≤ bound s R K/(1-ρ/s) := by
  obtain ⟨hM,hcoeff⟩ := eventually_coefficients (hρ.trans_lt hρs) hsR hR hK
  filter_upwards [hcoeff] with n hn
  intro T hT hE v hv
  exact ⟨WickCoefficientCauchy.weighted_summable hρ hρs hM (hn T hT hE v hv),
    WickCoefficientCauchy.weighted_tsum_bound hρ hρs hM (hn T hT hE v hv)⟩

end ActualWickCoefficientBounds
#print axioms ActualWickCoefficientBounds.eventually_weighted
