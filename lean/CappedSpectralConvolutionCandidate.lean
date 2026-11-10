import ActualScoreWeightsCandidate
import WeightedKernelInflationCandidate
import ActualGammaBoundsCandidate
import SummedGammaAbsorptionCandidate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace CappedSpectralConvolutionCandidate
open TournamentHamiltonian ActualTournamentPrescalingBounds TournamentPrescalingMassBound
open NonprincipalReconstructionCandidate
open scoped Classical

noncomputable def inflation (a0 K : ℝ) : ℝ :=
  Real.exp 1 * (1 / (1 - a0 ^ 2) + K) * weightedPrincipalMoment (ActualScoreWeightsCandidate.cap a0)
noncomputable def quadraticInflation (a0 K : ℝ) : ℝ :=
  (K + 2) * Real.exp 1 * ∑' k, subsetMoment (ActualScoreWeightsCandidate.cap a0) 2 k

theorem finite_spectral_upper {n : ℕ} (T : Tournament n)
    (N : ℕ) (hn : 1 ≤ n) (hN : 2 * N ≤ n) (a0 K : ℝ)
    (h0 : 0 ≤ a0) (h1 : a0 < 1) (hK : 0 ≤ K)
    (ha : ∀ i, |normalizedScore T i| ≤ a0)
    (hx : K * (Real.sqrt (tau (normalizedScore T) / n) + 1 / n) ≤ 1)
    (hsmall : (K + 2) * (N : ℝ) ^ 2 / n ≤ 1)
    (hper : ∀ U : Finset (Fin n), U.card < N →
      ((adjacency T).submatrix (Subtype.val : (Uᶜ : Finset (Fin n)) → Fin n) Subtype.val).permanent ≤
        gamma (normalizedScore T) * (∏ i ∈ U, (1+normalizedScore T i)⁻¹) *
          (∏ j ∈ U, (1-normalizedScore T j)⁻¹) *
            (((n - U.card).factorial : ℝ) / (2 : ℝ) ^ (n - U.card)) * gaussianFactor T *
              Real.exp (-1 + K * ActualPrincipalBudgetCandidate.budget n U.card (tau (normalizedScore T)))) :
    shortConvolution T N / meanPaths n ≤ spectralRatio T * gamma (normalizedScore T) * Real.exp
      (K * ActualPrincipalBudgetCandidate.budget n 0 (tau (normalizedScore T)) + inflation a0 K *
        (tau (normalizedScore T) / n + Real.sqrt (tau (normalizedScore T) / n) + 1 / n) +
          quadraticInflation a0 K / n) := by
  have hnpos : 0 < n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hτ := tau_nonneg (normalizedScore T)
  have hd : 0 < 1 - a0 ^ 2 := by nlinarith
  let x := K * (Real.sqrt (tau (normalizedScore T) / n) + 1 / n)
  let w := ActualScoreWeightsCandidate.weight T x
  let W := ActualScoreWeightsCandidate.cap a0
  let R := tau (normalizedScore T) / n + Real.sqrt (tau (normalizedScore T) / n) + 1 / n
  let C := Real.exp 1 * (1 / (1 - a0 ^ 2) + K)
  let D := quadraticInflation a0 K
  let Q := gamma (normalizedScore T) * gaussianFactor T * Real.exp (-1) *
    Real.exp (K * ActualPrincipalBudgetCandidate.budget n 0 (tau (normalizedScore T)))
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hw := ActualScoreWeightsCandidate.weight_bounds T a0 x h0 h1 hx0 hx ha
  have hW : 1 ≤ W := by
    have hdle : 1 - a0 ^ 2 ≤ 1 := by nlinarith [sq_nonneg a0]
    have h := (le_div_iff₀ hd).mpr (show 1 * (1 - a0 ^ 2) ≤ Real.exp 1 by
      have he := Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1); linarith)
    exact h
  have hGamma : 0 ≤ gamma (normalizedScore T) :=
    (ActualGammaBoundsCandidate.gamma_pos (normalizedScore T) a0 h0 h1 ha).le
  have hG := (gaussianFactor_bounds T hnpos).1.le
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hmoment : 0 ≤ ∑' k, subsetMoment W 2 k := tsum_nonneg (fun k => subsetMoment_nonneg (by linarith) 2 k)
  have hD : 0 ≤ D := by dsimp [D, quadraticInflation]; positivity
  have hexcess : (∑ i, (w i - 1)) / n ≤ C * R := by
    have h := ActualScoreWeightsCandidate.weight_excess T hnpos a0 x h0 h1 hx0 hx ha
    apply h.trans
    dsimp [C, R, x]
    have hrate : 0 ≤ tau (normalizedScore T) / (n : ℝ) := div_nonneg hτ hn0.le
    have hr : 0 ≤ Real.sqrt (tau (normalizedScore T) / n) + 1 / n := by positivity
    have hi : 0 ≤ 1 / (1 - a0 ^ 2) := by positivity
    have hh : (1 / (1 - a0 ^ 2)) * (tau (normalizedScore T) / n) +
        K * (Real.sqrt (tau (normalizedScore T) / n) + 1 / n) ≤
          (1 / (1 - a0 ^ 2) + K) *
            (tau (normalizedScore T) / n + Real.sqrt (tau (normalizedScore T) / n) + 1 / n) := by
      nlinarith [mul_nonneg hi hr, mul_nonneg hK hrate]
    have hm := mul_le_mul_of_nonneg_left hh (Real.exp_nonneg 1)
    convert hm using 1 <;> simp only [div_eq_mul_inv, mul_inv_rev] <;> ring
  have hquad : ∀ U : Finset (Fin n), U.card < N →
      ((adjacency T).submatrix (Subtype.val : (Uᶜ : Finset (Fin n)) → Fin n) Subtype.val).permanent ≤
        Q * (((n - U.card).factorial : ℝ) / (2 : ℝ) ^ (n - U.card)) * (∏ i ∈ U, w i) *
          Real.exp (K * (U.card : ℝ) ^ 2 / n) := by
    intro U hU
    have hu := hper U hU
    have hs : -1 + K * ActualPrincipalBudgetCandidate.budget n U.card (tau (normalizedScore T)) =
        (-1 + K * ActualPrincipalBudgetCandidate.budget n 0 (tau (normalizedScore T))) + (U.card : ℝ) * x +
          K * (U.card : ℝ) ^ 2 / n := by
      rw [ActualPrincipalBudgetCandidate.budget_card_split]
      dsimp [x]
      ring
    rw [hs] at hu
    simp only [Real.exp_add] at hu
    change _ ≤ Q * (((n - U.card).factorial : ℝ) / (2 : ℝ) ^ (n - U.card)) *
      (∏ i ∈ U, ActualScoreWeightsCandidate.weight T x i) * Real.exp (K * (U.card : ℝ) ^ 2 / n)
    rw [ActualScoreWeightsCandidate.weight_prod]
    convert hu using 1
    dsimp [Q]
    ring
  have hshort := shortConvolution_le_quadratic_weighted_mass T N hnpos hN K hK hsmall Q hQ
    w W (by linarith) (fun i => by have h := (hw i).1; linarith) (fun i => (hw i).2) hquad
  have hDnorm : ((K + 2) * Real.exp 1 / n) * (∑' k, subsetMoment W 2 k) = D / n := by
    dsimp [D, quadraticInflation, W]
    ring
  rw [hDnorm] at hshort
  have hinfl := weightedPrincipalMass_add_le_kernel_exp T hnpos w W hW (fun i => (hw i).1)
    (fun i => (hw i).2) C R D hC hR hD hexcess
  have hcombine := hshort.trans (mul_le_mul_of_nonneg_left hinfl (by positivity : 0 ≤ Q / 2))
  convert hcombine using 1
  dsimp [Q, C, R, D, W, inflation]
  rw [spectralRatio]
  simp only [Real.exp_add, Real.exp_neg]
  field_simp


/-- The summed exponent is dominated by the exact Gamma-absorption budget. -/
lemma summed_budget_le (n : ℕ) (τ K C D : ℝ) (hτ : 0 ≤ τ)
    (_hK : 0 ≤ K) (hC : 0 ≤ C) (hD : 0 ≤ D) :
    K*ActualPrincipalBudgetCandidate.budget n 0 τ+
      C*(τ/n+Real.sqrt (τ/n)+1/n)+D/n ≤
        (K+C+D)*SummedGammaAbsorptionCandidate.budget τ n := by
  let b := SummedGammaAbsorptionCandidate.budget τ n
  have hbase : ActualPrincipalBudgetCandidate.budget n 0 τ = b := by
    dsimp [b,ActualPrincipalBudgetCandidate.budget,SummedGammaAbsorptionCandidate.budget]
    ring
  have hR : τ/n+Real.sqrt (τ/n)+1/n ≤ b := by
    dsimp [b,SummedGammaAbsorptionCandidate.budget]
    have hsq : 0 ≤ τ^2/(n : ℝ) := by positivity
    have ht : 0 ≤ τ*Real.sqrt (τ/n) := mul_nonneg hτ (Real.sqrt_nonneg _)
    rw [add_div]
    linarith
  have hi : (1 : ℝ)/n ≤ b := by
    have hnonneg : 0 ≤ (τ+τ^2)/(n : ℝ)+τ*Real.sqrt (τ/n)+Real.sqrt (τ/n) := by positivity
    dsimp [b,SummedGammaAbsorptionCandidate.budget]
    linarith
  rw [hbase]
  have h1 := mul_le_mul_of_nonneg_left hR hC
  have h2 := mul_le_mul_of_nonneg_left hi hD
  change K*b+C*(τ/n+Real.sqrt (τ/n)+1/n)+D/n ≤ (K+C+D)*b
  calc
    _ ≤ K*b+C*b+D*b := by
      simpa only [mul_one_div] using add_le_add (add_le_add (le_refl (K*b)) h1) h2
    _ = _ := by ring

end CappedSpectralConvolutionCandidate

set_option pp.fullNames true
#check CappedSpectralConvolutionCandidate.inflation
#print axioms CappedSpectralConvolutionCandidate.inflation
#check CappedSpectralConvolutionCandidate.quadraticInflation
#print axioms CappedSpectralConvolutionCandidate.quadraticInflation
#check CappedSpectralConvolutionCandidate.finite_spectral_upper
#print axioms CappedSpectralConvolutionCandidate.finite_spectral_upper
#check CappedSpectralConvolutionCandidate.summed_budget_le
#print axioms CappedSpectralConvolutionCandidate.summed_budget_le
