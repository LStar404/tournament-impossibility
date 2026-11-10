import ActualCappedMinorUpperCandidate
import ActualReferenceGaussianBridge
import ActualGammaBoundsCandidate
/-! Finite Scalar absorption for the core-minor threshold. -/
set_option autoImplicit false
noncomputable section
namespace CoreMinorThresholdScalarCandidate
open TournamentHamiltonian ActualTournamentPrescalingBounds
open GeneralScalarRestorationCandidate

lemma gaussian_upper {n : ℕ} (T : Tournament n) (hn : 0 < n) :
    Real.exp (RealProjectionAggregationCandidate.g
      (SkewBaselineGramDifferenceCandidate.scaled (signMatrix T))) ≤ 2 := by
  rw [← ActualReferenceGaussianBridge.gaussianFactor_eq_exp_g T hn]
  exact (gaussianFactor_bounds T hn).2.le

lemma absorb_additive {g e d : ℝ} (hg : Real.exp g ≤ 2)
    (he : 0 ≤ e) (hd : 0 ≤ d) :
    Real.exp (g+e)+2*d ≤ 2*Real.exp (e+d) := by
  rw [Real.exp_add, Real.exp_add]
  have h1 : 1 ≤ Real.exp e := Real.one_le_exp_iff.mpr he
  have h2 : 1+d ≤ Real.exp d := by simpa only [add_comm] using Real.add_one_le_exp d
  nlinarith [mul_le_mul_of_nonneg_right hg (Real.exp_pos e).le,
    mul_le_mul_of_nonneg_left h2 (Real.exp_pos e).le]

lemma omittedGamma_upper {n : ℕ} (T : Tournament n) (I J : Finset (Fin n))
    {a0 : ℝ} (h0 : 0 ≤ a0) (h1 : a0 < 1)
    (ha : ∀ i, |normalizedScore T i| ≤ a0) :
    omittedGamma T I J ≤
      (∏ i∈I,(1+normalizedScore T i)⁻¹)*(∏ j∈J,(1-normalizedScore T j)⁻¹) := by
  have hG := ActualGammaBoundsCandidate.gamma_le_one (normalizedScore T) a0 h0 h1 ha
  have hL : 0 ≤ ∏ i∈I,(1+normalizedScore T i)⁻¹ := by
    apply Finset.prod_nonneg; intro i hi
    apply inv_nonneg.mpr
    linarith [(abs_le.mp (ha i)).1]
  have hR : 0 ≤ ∏ j∈J,(1-normalizedScore T j)⁻¹ := by
    apply Finset.prod_nonneg; intro j hj
    apply inv_nonneg.mpr
    linarith [(abs_le.mp (ha j)).2]
  unfold omittedGamma
  simpa using mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hG hL) hR
end CoreMinorThresholdScalarCandidate
